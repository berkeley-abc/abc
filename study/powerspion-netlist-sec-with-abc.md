# PowerSpion write_netlist 출력으로 ABC SEC 수행하기

- 작성일: 2026-07-04
- 질문: PowerSpion의 `write_netlist` 명령으로 생성한 netlist 2개를 Berkeley ABC의 입력으로 사용해 SEC(Sequential Equivalence Checking)를 수행할 수 있는가?
- 검증 방법: 로컬 소스 분석(PowerSpion writer + ABC 파서) + 공식 문서/논문 교차 검증(25개 claim, 3-표 검증 전원 통과, 반박 0)

## 0. 결론 요약

| 경로 | 가능 여부 | 비고 |
|---|---|---|
| `write_netlist` 출력 → ABC `read_verilog` 직접 | ❌ 불가 | 파싱은 되지만 liberty 셀이 blackbox가 되어 SEC 불능 |
| `write_netlist` 출력 → **Yosys 변환** → ABC `dsec`/`pdr` | ✅ 가능 | 검증된 표준 경로 (§4, §5) |
| `write_netlist` 출력 → **EQY** | ✅ 가능 | 공식 권장 도구, 내부적으로 ABC pdr 구동 (§6) |

---

## 1. 사전 지식 — 처음 접하는 사람을 위한 배경

### 1.1 ABC가 다루는 "회로"는 RTL이 아니다

ABC는 **Boolean logic network**만 다룬다. 즉:

- **PI/PO** (primary input/output): 회로의 입출력 단자
- **내부 노드**: 각각 하나의 Boolean 함수 (AND, OR, ... 의 조합)
- **Latch**: D-플립플롭 1비트 (초기값 0/1/don't-care 포함)

`always @(posedge clk)`, `if/case`, 비트폭 연산, 모듈 계층 같은 RTL 개념은 존재하지 않는다.
클럭조차 명시적으로 없다 — "모든 latch가 매 cycle 동시에 업데이트된다"는 **암묵적 단일 클럭 모델**이다.
내부적으로는 회로를 **AIG**(And-Inverter Graph: 2-입력 AND 노드 + 에지의 인버터 표시만으로
모든 조합논리를 표현하는 그래프)로 변환해 최적화/검증을 수행한다.

이 모델 제약이 이 문서 전체를 관통하는 핵심이다: **ABC에 넣으려면 모든 것이
"AND/NOT + 단순 D-FF"로 환원되어야 한다.**

### 1.2 CEC vs SEC

- **CEC** (Combinational EC): 레지스터 위치가 같은 두 회로에서, 레지스터 사이의
  조합논리만 비교. 빠르지만 레지스터가 이동/재인코딩되면 사용 불가.
- **SEC** (Sequential EC): 상태(레지스터)까지 포함해 "리셋 후 모든 입력 시퀀스에 대해
  출력 시퀀스가 같은가"를 증명. retiming·FSM 재인코딩까지 커버하지만 PSPACE-hard라
  unbounded 증명이 실패할 수 있다.

### 1.3 등장하는 파일 포맷

#### structural Verilog (.v) — PowerSpion write_netlist의 출력

논리를 전부 **셀 인스턴스 + 배선**으로만 표현한 Verilog. RTL(behavioral) 구문이 없다.

```verilog
module top (a, b, clk, out);
  input a, b, clk;
  output out;
  wire n1;
  NAND2X1 u1 ( .A(a), .B(b), .Y(n1) );          // liberty 셀 인스턴스
  DFFX1   u2 ( .D(n1), .CK(clk), .Q(out) );     // 이름 기반 포트 연결
endmodule
```

핵심: `NAND2X1`이 무슨 논리인지는 이 파일에 없다. **셀의 기능 정의는 Liberty 파일에 있다.**

#### Liberty (.lib) — 표준 셀 라이브러리

파운드리/라이브러리 벤더가 제공하는 셀 정의. 타이밍/전력 외에 **논리 기능**도 들어 있다:

```
cell (NAND2X1) {
  pin (Y) { direction: output; function: "!(A & B)"; }   /* 조합 셀: function 속성 */
  ...
}
cell (SDFFX1) {
  ff (IQ, IQN) {                    /* 순차 셀: ff 그룹 */
    clocked_on: "CK";
    next_state: "(SE) ? SI : D";    /* scan mux까지 함수로 인코딩됨 */
  }
  ...
}
```

#### BLIF (.blif) — Berkeley Logic Interchange Format

Boolean network를 사람이 읽을 수 있게 쓴 텍스트 포맷. `.names`(노드의 truth table),
`.latch`(D-FF + 초기값)로 구성. ABC/Yosys 둘 다 읽고 쓴다.

```
.model example
.inputs a b
.outputs out
.names a b t      # t = a AND b  (11 -> 1)
11 1
.latch t out 0    # D-FF: 입력 t, 출력 out, 초기값 0
.end
```

#### AIGER (.aig) — AIG의 표준 포맷

모델체킹 대회 표준의 바이너리 포맷. AND 게이트 + latch + (선택적으로) bad-state
property만 담는다. 사람이 못 읽는 대신 매우 컴팩트하다. 이 문서의 플로우에서
**Yosys → ABC로 회로를 넘기는 운반체**로 쓰인다.

#### genlib — ABC의 조합 셀 라이브러리 포맷

ABC가 mapped netlist를 읽을 때 쓰는 단순 텍스트 라이브러리.
**조합 게이트만 정의할 수 있고, latch/FF는 정의해도 무시된다** (§3 참고).

### 1.4 등장하는 도구

- **ABC** (berkeley-abc/abc): 논리 합성·검증 **엔진**. HDL 컴파일러가 아니다.
  SEC 엔진(`dsec`, `pdr` 등)이 여기 있다.
- **Yosys** (YosysHQ/yosys): 오픈소스 합성 프레임워크. Verilog/Liberty를 파싱·elaboration
  하는 **프론트엔드** 역할. 이 문서에서는 "PowerSpion netlist를 ABC가 먹을 수 있는
  형태(AIGER)로 변환하는 어댑터"로 쓴다.
- **EQY** (YosysHQ/eqy): Yosys 기반 등가검증 전용 도구. gold(기준) vs gate(비교 대상)
  두 디자인을 받아 partition 단위로 증명한다.
- **SBY** (SymbiYosys): Yosys 기반 formal 검증 드라이버. EQY가 내부적으로 사용하며,
  `engine abc pdr` 설정으로 ABC의 IC3/PDR 엔진을 구동할 수 있다.

---

## 2. 질문과 결론

**질문**: PowerSpion `write_netlist`가 생성한 netlist 2개(예: 어떤 순차 변환 전/후)를
ABC에 넣어 SEC를 수행할 수 있는가?

**결론**: ABC에 **직접** 넣는 것은 불가능하다. 그러나 **Yosys를 변환 프론트엔드로**
사용하면 가능하며, 검증된 경로가 3가지 있다 (§4, §5, §6).

## 3. 왜 ABC 직접 입력은 안 되는가

### 3.1 write_netlist 출력의 특성 (writer 소스 분석)

`cmd_write_netlist.cpp`는 module 골격을 쓰고, 실제 문장 생성은
`NetlistInst::to_verilog()` 계열에 위임한다. 출력 형태:

- 계층 유지 (모듈 인스턴스 + leaf 셀 인스턴스), **이름 기반 포트 연결만** 사용
- leaf 인스턴스의 reference는 **liberty 셀 이름 문자열** (`NetlistInst.cpp:903`)
- tie-off는 `.A(1'b0)` / `.A(1'b1)` / `.A(1'bx)` 리터럴 (`NetlistInst.cpp:557-579`)
- 미연결 leaf 핀은 `.Q(UNCONNECTED_1)` 같은 생성 이름 (`NetlistInst.cpp:831`)
- bus는 `[msb:lsb]` 슬라이스와 `{...}` concatenation으로 출력 (`NetlistInst.cpp:589`)
- `assign`/`defparam`/`specify`/parameter는 일절 출력하지 않음

예시 (leaf 셀 한 줄):

```verilog
SDFFRX2 U123 ( .D(n5), .CK(clk), .Q(n6), .QN(UNCONNECTED_1), .RN(1'b1) );
```

이 문법 자체는 ABC의 Verilog 파서(IWLS 2002/2005 subset)가 처리할 수 있는 범위다
(상수: `verCore.c:753`, concat: `verCore.c:1820`, bit-select: `verCore.c:1873`).
**문제는 문법이 아니라 의미론이다.**

### 3.2 ABC 쪽의 세 가지 벽

1. **정의 없는 모듈은 blackbox가 된다** (`abc/src/base/ver/verCore.c:292-330`).
   `SDFFRX2` 같은 셀의 정의가 파일에 없으므로 ABC는 속이 빈 상자로 취급한다.
   회로 논리가 통째로 사라지므로 등가검증이 성립하지 않는다.

2. **genlib으로도 순차 셀은 해결 불가**. `read_verilog -m`(mapped 모드) + `read_genlib`
   조합이면 조합 셀은 논리로 연결되지만, ABC의 genlib 파서는 `LATCH` 구문을
   **명시적으로 skip**한다 (`abc/src/map/mio/mioRead.c:242-252`, "Skipping latch...").
   FF/latch/ICG 셀을 ABC latch로 만들 방법이 없다.

3. **ABC의 순차 모델 제약**: 단일 클럭(클럭 자체는 추상화되어 사라짐) +
   **초기값이 알려진** D-FF만 허용한다. don't-care 초기값은 경고와 함께 0으로 강제된다
   (`abc/src/base/abci/abcDar.c:268-281`; Brayton & Mishchenko, CAV'10).

---

## 4. 경로 A — Yosys 변환 → ABC `dsec`

### 원리

Yosys의 `read_liberty`를 **full 모드**(`-lib` 옵션 없이)로 실행하면:

- 조합 셀: liberty `function` 속성 → 실제 게이트 논리로 변환
- 순차 셀: liberty `ff` 그룹 → Yosys DFF 셀로 변환. SDFF의 scan mux도 `next_state`
  함수에 인코딩되어 있으므로 DFF + mux 논리로 올바르게 들어온다

즉 §3의 벽 1, 2가 Yosys 쪽에서 해소된다. 이후 AIGER로 내보내 ABC에 전달한다.

주의: `read_liberty -lib`은 **빈 blackbox만** 만든다 (합성용 링크 정보).
등가검증 목적에는 반드시 `-lib` 없이 읽어야 한다.

### 명령 시퀀스 (netlist 하나당 한 번 실행)

```tcl
# conv.ys — 실행: yosys -s conv.ys
read_verilog netlist_before.v      # PowerSpion 출력 읽기
read_liberty stdcells.lib          # 셀 기능 정의 로드 (full 모드; -lib 금지)
hierarchy -top TOP                 # top 모듈 지정, 계층 해석
flatten                            # 계층 제거 (AIGER는 flat만 허용)
async2sync                         # async set/reset FF -> sync 로직으로 변환
dffunmap                           # 복합 FF 셀 -> 단순 FF로 분해
aigmap                             # 모든 조합논리 -> AND/NOT (AIG 프리미티브)로 변환
write_aiger -symbols before.aig    # AIGER로 저장 (-symbols: 포트 이름 보존, dsec 매칭용)
```

`after.aig`도 동일하게 생성한 뒤:

```bash
./abc -c "dsec -v before.aig after.aig"
# 출력: "Networks are equivalent." 또는 "Networks are NOT EQUIVALENT" (+ 반례)
```

`dsec`는 기본적으로 **PI/PO를 이름으로 매칭**한다 (`abc/src/base/abci/abcMiter.c:66`).
두 netlist가 같은 PowerSpion에서 나왔으므로 포트 이름이 유지되면 그대로 작동하고,
이름이 달라졌으면 `-n` 옵션(순서 매칭)으로 전환한다.

---

## 5. 경로 B — Yosys에서 miter 생성 → ABC `pdr`

**miter**란: 두 회로의 같은 입력을 묶고, 대응 출력들을 XOR로 비교해 "하나라도 다르면
1이 되는 출력" 하나로 합친 회로. 등가검증은 "miter 출력이 절대 1이 될 수 없다"의
증명으로 환원된다.

이 경로는 포트 매칭을 Yosys가 miter를 만들 때 수행하므로, ABC 쪽 이름 매칭 문제를
우회한다. `write_aiger -miter`는 출력을 AIGER의 bad-state property로 기록하므로
ABC에서는 model checker(`pdr` = IC3)만 돌리면 된다.

```tcl
# miter.ys
read_verilog netlist_before.v
read_liberty stdcells.lib
prep -top TOP; flatten
rename TOP gold                    # 기준 디자인 이름 변경
design -stash gold                 # 임시 저장

read_verilog netlist_after.v
read_liberty stdcells.lib
prep -top TOP; flatten
rename TOP gate
design -stash gate

design -copy-from gold -as gold gold   # 두 디자인을 한 세션에 로드
design -copy-from gate -as gate gate
miter -equiv -flatten gold gate miter  # 등가검증 miter 생성
hierarchy -top miter
async2sync; dffunmap; aigmap
write_aiger -miter miter.aig           # 출력을 bad-state property로 기록
```

```bash
./abc -c "read_aiger miter.aig; pdr -v"
# "Property proved" = 등가.  반례가 나오면 = 불일치 (반례 시퀀스 제공)
```

---

## 6. 경로 C — EQY (권장)

Yosys 공식 문서는 raw `miter`+`sat` 대신 전용 도구 SBY/EQY 사용을 명시적으로
권장한다. EQY가 이 시나리오에 잘 맞는 이유:

- `[gold]`/`[gate]` 섹션에 §4의 read 명령을 그대로 쓰면 된다
- **이름 매칭 규칙을 wildcard/regex로 직접 제어** (`gold-match` 규칙, bus 비트는
  `[]` 토큰) — 두 netlist 세대 간 이름 mangling의 공식 해결책
- 문제를 partition으로 분할하고, partition별로 SBY의 `engine abc pdr`(IC3)로
  unbounded 증명 — 내부적으로 ABC를 구동하므로 사용자가 dsec를 만질 필요가 없다
- 제약: partition 방식은 내부 대응점 매칭을 전제하므로 **retiming에는 비관용적**.
  같은 generator가 만든 구조적으로 유사한 두 netlist라는 본 케이스에는 오히려 적합

```ini
; compare.eqy — 실행: eqy compare.eqy
[gold]
read_verilog netlist_before.v
read_liberty stdcells.lib
prep -top TOP

[gate]
read_verilog netlist_after.v
read_liberty stdcells.lib
prep -top TOP

[script]
prep
async2sync

[strategy pdr]
use sby
engine abc pdr
```

참고: 공식 spm 예제는 `read_liberty` 대신 표준셀의 **Verilog simulation model**을
읽는 변형을 보여준다. liberty import가 말썽일 때 쓸 수 있는 우회로다.

---

## 7. PowerSpion 출력 특성별 주의점

| 특성 | 근거 (writer 코드) | 영향 및 대응 |
|---|---|---|
| `1'bx` tie-off 출력 가능 | `NetlistInst.cpp:579` | Yosys에서 x는 최적화 자유도로 해석됨. SEC 전에 `setundef -zero` 등으로 양쪽을 동일하게 고정 |
| `UNCONNECTED_n` (선언 없는 wire) | `NetlistInst.cpp:831` | Verilog implicit net 규칙으로 Yosys가 수용. `clean`이 정리. 문제 없음 |
| 미연결 **모듈 포트는 생략**됨 | `NetlistInst.cpp:747` | leaf 셀 포트(`UNCONNECTED_n`)와 비대칭. 두 netlist에서 생략 양상이 다르면 인터페이스 불일치 가능 |
| escaped identifier를 저장된 그대로 출력 | writer는 `\` 추가/제거 안 함 | 특수문자 이름에 escape가 없으면 Yosys 파싱 실패. 실제 덤프로 확인 필요 |
| 레지스터 초기값 미출력 (initial 없음) | writer 전체 | ABC는 known-init 모델. 양쪽 모두 0-init으로 통일하거나 reset 시퀀스 기반 등가로 접근 |

**추가 경고 (교차 검증 확정)**:

1. **멀티클럭은 조용히 합쳐진다**: `write_aiger`는 async FF·latch·미변환 셀에는
   hard error를 내지만, 서로 다른 클럭의 FF들은 **경고 없이** AIGER의 단일 암묵
   클럭으로 collapse된다. 클럭 도메인이 2개 이상이면 `async2sync` 대신
   `clk2fflogic`을 사용하고(클럭 토글이 명시적 상태가 되어 증명 비용 증가),
   클럭 도메인 구성은 수동으로 감사할 것.
2. **ICG(clock gating) 셀**: liberty ICG는 보통 latch+AND 구조다. `read_liberty`의
   latch 그룹 import 동작은 이번 검증에서 확인되지 않은 영역이므로, ICG 포함
   netlist는 첫 실험에서 변환 결과를 반드시 확인할 것. gated clock이 생기므로
   `clk2fflogic` 경로가 필요할 가능성이 높다.

---

## 8. 검증 절차 (smoke test)

처음 플로우를 세울 때 권장하는 순서:

1. **Self-SEC**: PowerSpion에서 같은 디자인을 두 번 `write_netlist` → 경로 A로 비교
   → "Networks are equivalent"가 나와야 정상 (변환 파이프라인 자체 검증)
2. **음성 대조군**: 한쪽 netlist의 셀 하나를 바꾸거나 tie 값을 뒤집어
   → "NOT EQUIVALENT" + 반례가 나오는지 확인
3. 그 다음 실제 비교 대상(변환 전/후)에 적용

`dsec`가 시간 내에 못 풀면: `dprove`(다단계 엔진 파이프라인), miter + `pdr`(경로 B),
EQY partition 방식(경로 C) 순으로 시도. 그래도 안 되면 BMC(`bmc3`)로 bounded 확인만
가능하다는 결론도 유효한 결과다.

---

## 9. 출처

**로컬 소스** (판정의 1차 근거):

- PowerSpion: `pb/master/source/cmd/cmd_write_netlist.cpp`,
  `pb/master/source/design/netlist/src/database/NetlistInst.cpp` (writer 문법)
- ABC: `src/base/ver/verCore.c` (Verilog 파서, blackbox 처리),
  `src/map/mio/mioRead.c:242-252` (genlib LATCH skip),
  `src/base/abci/abcMiter.c`, `src/base/abc/abcCheck.c` (miter 이름 매칭),
  `src/base/abci/abcDar.c:268-281` (don't-care init 0 강제)

**공식 문서/논문** (웹 교차 검증, 25 claim 확정):

- Yosys 명령 문서: `write_aiger`, `read_liberty`, `clk2fflogic`, `async2sync`,
  equiv_* passes — https://yosyshq.readthedocs.io/projects/yosys/
- Yosys model checking 가이드 (miter+sat 플로우, SBY/EQY 권장) —
  https://yosyshq.readthedocs.io/projects/yosys/en/latest/using_yosys/more_scripting/model_checking.html
- EQY 문서/예제 (quickstart, strategies, spm 예제) —
  https://yosyshq.readthedocs.io/projects/eqy/
- R. Brayton, A. Mishchenko, "ABC: An Academic Industrial-Strength Verification Tool",
  CAV 2010 — https://people.eecs.berkeley.edu/~alanmi/publications/2010/cav10_abc.pdf
- YosysHQ/yosys issues #2850 (async FF write_aiger 에러), #3428 (equiv_* 실패 사례)
