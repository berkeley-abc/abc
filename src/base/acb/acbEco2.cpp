/**CFile****************************************************************

  FileName    [acbEco2.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Rectification by cofactoring, simulation and SAT refinement.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 27, 2026.]

***********************************************************************/

#include <algorithm>
#include <cerrno>
#include <cctype>
#include <cmath>
#include <climits>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <filesystem>
#if defined(_WIN32)
#include <io.h>
#else
#include <unistd.h>
#endif
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "base/abcc/abcc.h"
#include "misc/util/utilSignal.h"
#include "misc/util/utilTruth.h"
#include "base/io/ioResub.h"
#include "bool/kit/kit.h"
#include "aig/gia/giaAig.h"
#include "proof/cec/cec.h"
#include "sat/glucose3/AbcGlucose3.h"

ABC_NAMESPACE_IMPL_START

namespace {

using std::string;
using std::vector;
using Ints = vector<int>;
using Words = vector<word>;
enum Gate { UNDEF, PI, TARGET, ZERO, ONE, BUF, INV, AND, NAND, OR, NOR, XOR, XNOR };
static const char * const GateName[] = { "", "", "", "", "", "buf", "not", "and", "nand", "or", "nor", "xor", "xnor" };

struct Net {
    string name;
    Gate type = UNDEF;
    Ints fanins;
    int weight = -1, lit = -1;
    bool blocked = false;
    explicit Net( const string & s ) : name(s) {}
};

static bool Number( const string & s, int & n )
{
    char * end;
    errno = 0;
    long val = strtol(s.c_str(), &end, 10);
    if ( errno || end == s.c_str() || *end || val < 0 || val > INT_MAX )
        return false;
    n = (int)val;
    return true;
}

/**Function*************************************************************

  Synopsis    [Reads scalar structural Verilog, retaining the physical net names.]

  Description [The scanner belongs to this input. Declarations and drivers
  may be out of order. The original source is retained for patch insertion.]

***********************************************************************/
struct Circuit {
    string text, module, error;
    size_t pos = 0, start = 0, endmodule = 0;
    std::unordered_map<string,int> ids;
    std::set<string> instances;
    vector<Net> nets;
    Ints pis, posNets, targets, order;

    int net( const string & name ) {
        auto it = ids.find(name);
        if ( it != ids.end() ) return it->second;
        int id = (int)nets.size();
        ids[name] = id; nets.emplace_back(name);
        return id;
    }
    string token() {
        while ( pos < text.size() ) {
            if ( isspace((unsigned char)text[pos]) ) { ++pos; continue; }
            if ( text.compare(pos, 2, "//") == 0 ) {
                pos = text.find('\n', pos+2);
                if ( pos == string::npos ) pos = text.size();
                continue;
            }
            if ( text.compare(pos, 2, "/*") == 0 ) {
                pos = text.find("*/", pos+2);
                if ( pos == string::npos ) { pos = text.size(); error = "unterminated comment"; }
                else pos += 2;
                continue;
            }
            break;
        }
        start = pos;
        if ( pos == text.size() ) return "";
        char c = text[pos++];
        if ( c == '[' ) {
            string index(1,c);
            while ( pos < text.size() && text[pos] != ']' ) {
                char d = text[pos++];
                if ( !isspace((unsigned char)d) ) index += d;
            }
            if ( pos == text.size() ) { error = "unterminated bit select"; return ""; }
            ++pos;
            return index + "]";
        }
        if ( c == '\\' ) {
            while ( pos < text.size() && !isspace((unsigned char)text[pos]) ) ++pos;
        } else if ( !strchr("(),;=", c) ) {
            while ( pos < text.size() && !isspace((unsigned char)text[pos]) &&
                    !strchr("(),;=/[", text[pos]) ) ++pos;
        }
        return text.substr(start, pos-start);
    }
    bool declare( const string & s, const string & op, bool impl ) {
        int id = net(s);
        if ( op == "input" ) {
            if ( nets[id].type != UNDEF ) { error = "multiple drivers for " + s; return false; }
            nets[id].type = PI; pis.push_back(id);
        } else if ( op == "output" ) posNets.push_back(id);
        else if ( impl && s.compare(s[0] == '\\' ? 1 : 0,2,"t_") == 0 && nets[id].type == UNDEF ) {
            nets[id].type = TARGET; targets.push_back(id);
        }
        return true;
    }
    bool read( const char * path, bool impl ) {
        std::ifstream f(path, std::ios::binary);
        if ( !f ) { error = "cannot open file"; return false; }
        f.seekg(0,std::ios::end);
        std::streamoff length = f.tellg();
        if ( length < 0 ) { error = "cannot determine input size"; return false; }
        text.resize((size_t)length);
        f.seekg(0);
        if ( length && !f.read(&text[0],length) ) { error = "cannot read file"; return false; }
        if ( token() != "module" || (module = token()).empty() ) { error = "expected module"; return false; }
        std::unordered_set<string> ports;
        string s;
        while ( !(s = token()).empty() && s != ";" ) {
            if ( s == "(" || s == "," || s == ")" ) continue;
            if ( s == "input" || s == "output" ) { error = "expected separate port declarations"; return false; }
            if ( !ports.insert(s).second ) { error = "duplicate port " + s; return false; }
        }
        for (;;) {
            string op = token();
            if ( op == "endmodule" ) { endmodule = start; break; }
            if ( op.empty() ) { error = "expected endmodule"; return false; }
            bool decl = op == "wire" || op == "input" || op == "output";
            Gate type = UNDEF;
            for ( int k = BUF; k <= XNOR; ++k )
                if ( op == GateName[k] ) type = (Gate)k;
            if ( op == "assign" ) type = BUF;
            if ( !decl && type == UNDEF ) { error = "unsupported statement " + op; return false; }
            if ( !decl && op != "assign" ) {
                s = token();
                if ( s != "(" ) { instances.insert(s); s = token(); }
                if ( s != "(" ) { error = "expected gate ports"; return false; }
            }
            Ints pins;
            int first = -1, last = -1;
            while ( !(s = token()).empty() && s != ";" ) {
                if ( s == "," || s == ")" || s == "=" ) continue;
                if ( s[0] == '[' ) {
                    size_t colon = s.find(':');
                    if ( decl && colon != string::npos && first < 0 &&
                         Number(s.substr(1,colon-1),first) && Number(s.substr(colon+1,s.size()-colon-2),last) )
                        continue;
                    if ( !decl && !pins.empty() && colon == string::npos ) {
                        string bus = nets[pins.back()].name;
                        pins.back() = net(bus+s);
                        continue;
                    }
                    error = "invalid bit range " + s; return false;
                }
                if ( (op == "input" || op == "output") && !ports.erase(s) ) {
                    error = "unexpected port declaration " + s; return false;
                }
                if ( !decl ) pins.push_back(net(s));
                else if ( first < 0 ) {
                    if ( !declare(s,op,impl) ) return false;
                } else {
                    for ( int bit = last; ; bit += first > last ? 1 : -1 ) {
                        if ( !declare(s+"["+std::to_string(bit)+"]",op,impl) ) return false;
                        if ( bit == first ) break;
                    }
                }
            }
            if ( s.empty() ) { error = "unterminated statement"; return false; }
            if ( !decl ) {
                if ( pins.size() < 2 || ((type == BUF || type == INV) && pins.size() != 2) ) {
                    error = "invalid primitive pin count"; return false;
                }
                Net & n = nets[pins[0]];
                if ( n.type != UNDEF ) { error = "multiple drivers for " + n.name; return false; }
                n.type = type; n.fanins.assign(pins.begin()+1, pins.end());
            }
        }
        if ( !ports.empty() ) { error = "undeclared port " + *ports.begin(); return false; }
        if ( !token().empty() || !error.empty() ) { error = "expected one module"; return false; }
        for ( Net & n : nets ) {
            if ( n.name == "1'b0" || n.name == "1'h0" ) n.type = ZERO;
            if ( n.name == "1'b1" || n.name == "1'h1" ) n.type = ONE;
        }
        // Iterative topological sort also detects cycles and undriven fanins.
        vector<Ints> users(nets.size());
        Ints pending(nets.size());
        for ( int i = 0; i < (int)nets.size(); ++i ) {
            pending[i] = (int)nets[i].fanins.size();
            for ( int j : nets[i].fanins ) users[j].push_back(i);
            if ( !pending[i] && nets[i].type != UNDEF ) order.push_back(i);
        }
        for ( size_t k = 0; k < order.size(); ++k )
            for ( int j : users[order[k]] ) if ( !--pending[j] ) order.push_back(j);
        for ( int i = 0; i < (int)nets.size(); ++i )
            if ( pending[i] ) { error = "cycle or missing driver at " + nets[i].name; return false; }
        for ( int i : posNets )
            if ( nets[i].type == UNDEF ) { error = "undriven output " + nets[i].name; return false; }
        return true;
    }
    bool weights( const char * path ) {
        if ( !path ) { for ( Net & n : nets ) n.weight = 1; return true; }
        std::ifstream f(path);
        if ( !f ) { error = "cannot open weights"; return false; }
        string name, val;
        while ( f >> name ) {
            auto it = ids.find(name);
            if ( it == ids.end() ) it = ids.find(name[0] == '\\' ? name.substr(1) : "\\" + name);
            int cost;
            if ( it == ids.end() || !(f >> val) || !Number(val,cost) ) {
                error = "invalid weight for " + name; return false;
            }
            nets[it->second].weight = cost;
        }
        return !f.bad();
    }
};

struct Rand {
    word state = ABC_CONST(0x9e3779b97f4a7c15);
    word next() { state ^= state >> 12; state ^= state << 25; state ^= state >> 27;
        return state * ABC_CONST(0x2545f4914f6cdd1d); }
};

struct Node { int a, b; bool isXor; word deps, sig; };
static word Phase( word value, int lit ) { return (lit & 1) ? ~value : value; }
static word Key( int a, int b ) { return ((word)(unsigned)a << 32) | (unsigned)b; }

/**Function*************************************************************

  Synopsis    [Structurally hashed AND/XOR graph with incremental SAT checking.]

  Description [Each solver only sees gates in queried cones. Simulation
  proposes equivalences between designs; both polarities are SAT-checked
  before an equivalence can be used in hashing.]

***********************************************************************/
struct Graph {
    vector<Node> nodes;
    Ints vars, inputs;
    std::unordered_map<word,int> gates[2], classes;
    bmcg3_sat_solver * sat = bmcg3_sat_solver_start();
    Rand rng;
    abctime deadline;
    int checked = 0, merged = 0;
    bmcg3_sat_solver * fallback = NULL;
    Ints fallbackVars;
    bool lastFallback = false;
    bool sweeping = false, index = true, circuit;

    explicit Graph( abctime limit, bool useCircuit = true ) : deadline(limit), circuit(useCircuit) {
        nodes.push_back({-1,-1,false,0,0}); vars.push_back(-1); classes[0] = 0;
        bmcg3_sat_solver_set_jftr(sat,circuit ? 2 : 0);
        bmcg3_sat_solver_eliminate(sat,1);
        bmcg3_sat_solver_set_unit_justification(sat,0);
        vars[0] = bmcg3_sat_solver_addvar(sat);
        int unit = 1;
        bmcg3_sat_solver_addclause(sat,&unit,1);
        if ( limit ) bmcg3_sat_solver_set_runtime_limit(sat,limit);
    }
    ~Graph() { bmcg3_sat_solver_stop(sat); if ( fallback ) bmcg3_sat_solver_stop(fallback); }
    bool expired() const { return deadline && Abc_Clock() >= deadline; }
    int input( word mask ) {
        int lit = 2*(int)nodes.size();
        nodes.push_back({-1,-1,false,mask,rng.next()}); vars.push_back(-1);
        inputs.push_back(lit);
        word sig = nodes.back().sig;
        classes[Phase(sig,(int)(sig & 1))] = lit ^ (int)(sig & 1);
        return lit;
    }
    int satLit( int lit ) {
        int id = lit >> 1;
        if ( vars[id] < 0 ) {
            Node n = nodes[id];
            int a = -1, b = -1;
            if ( n.a >= 0 ) { a = satLit(n.a); b = satLit(n.b); }
            int v = vars[id] = bmcg3_sat_solver_addvar(sat);
            if ( n.a >= 0 && !circuit ) {
                if ( n.isXor ) bmcg3_sat_solver_add_xor(sat,v,a>>1,b>>1,(a^b)&1);
                else bmcg3_sat_solver_add_and(sat,v,a>>1,b>>1,a&1,b&1,0);
            } else if ( n.a >= 0 ) {
                // Glucose3 identifies an XOR by descending fanin literals.
                if ( (a > b) != n.isXor ) std::swap(a,b);
                bmcg3_sat_solver_set_var_fanin_lit(sat,v,a,b);
            }
        }
        return 2*vars[id] + (lit&1);
    }
    int cnfLit( int lit ) {
        int id = lit>>1;
        if ( fallbackVars[id] < 0 ) {
            Node n = nodes[id];
            int a = -1, b = -1;
            if ( n.a >= 0 ) { a = cnfLit(n.a); b = cnfLit(n.b); }
            int v = fallbackVars[id] = bmcg3_sat_solver_addvar(fallback);
            if ( !id ) { int unit = 2*v+1; bmcg3_sat_solver_addclause(fallback,&unit,1); }
            else if ( n.a >= 0 ) {
                if ( n.isXor ) bmcg3_sat_solver_add_xor(fallback,v,a>>1,b>>1,(a^b)&1);
                else bmcg3_sat_solver_add_and(fallback,v,a>>1,b>>1,a&1,b&1,0);
            }
        }
        return 2*fallbackVars[id]+(lit&1);
    }
    void prepareCnf() {
        if ( !fallback ) {
            fallback = bmcg3_sat_solver_start();
            if ( deadline ) bmcg3_sat_solver_set_runtime_limit(fallback,deadline);
        }
        fallbackVars.resize(nodes.size(),-1);
    }
    bool implies( int off, const Ints & cube, Ints & core, int budget ) {
        if ( expired() ) return false;
        prepareCnf();
        Ints lits(1,cnfLit(off));
        std::unordered_map<int,int> inverse;
        for ( int lit : cube ) {
            int a = cnfLit(lit);
            lits.push_back(a); inverse[a^1] = lit;
        }
        bmcg3_sat_solver_set_conflict_budget(fallback,budget);
        if ( bmcg3_sat_solver_solve(fallback,lits.data(),(int)lits.size()) != GLUCOSE3_UNSAT ) return false;
        int * reason;
        int n = bmcg3_sat_solver_final(fallback,&reason);
        core.clear();
        for ( int i = 0; i < n; ++i ) {
            auto it = inverse.find(reason[i]);
            if ( it != inverse.end() ) core.push_back(it->second);
        }
        return true;
    }
    int ask( int a, int b = 1, int budget = 0 ) {
        if ( a == 0 || b == 0 || a == (b^1) ) return GLUCOSE3_UNSAT;
        if ( expired() ) return GLUCOSE3_UNDEC;
        int lits[2];
        // A query on primary inputs has no gates to justify. Use ordinary
        // assumptions there, including for the all-constant SAT witness.
        if ( nodes[a>>1].a >= 0 || nodes[b>>1].a >= 0 ) {
            lits[0] = satLit(a); lits[1] = satLit(b);
            int roots[2] = {lits[0]>>1,lits[1]>>1};
            if ( circuit ) bmcg3_sat_solver_select_cones(sat,roots,2);
            lastFallback = false;
            bmcg3_sat_solver_set_conflict_budget(sat,budget ? budget : 300);
            int res = bmcg3_sat_solver_solve(sat,lits,2);
            if ( res != GLUCOSE3_UNDEC || budget || expired() ) return res;
        }
        prepareCnf();
        bmcg3_sat_solver_set_conflict_budget(fallback,budget);
        lastFallback = true;
        lits[0] = cnfLit(a); lits[1] = cnfLit(b);
        return bmcg3_sat_solver_solve(fallback,lits,2);
    }
    int gate( int a, int b, bool x = false ) {
        if ( a == b ) return x ? 0 : a;
        if ( a == (b^1) ) return x ? 1 : 0;
        if ( a < 2 ) return x ? b^a : a ? b : 0;
        if ( b < 2 ) return x ? a^b : b ? a : 0;
        if ( !x && (a&b&1) ) {
            Node l = nodes[a>>1], r = nodes[b>>1];
            if ( l.a >= 0 && r.a >= 0 && !l.isXor && !r.isXor &&
                 (((l.a^r.a)==1 && (l.b^r.b)==1) || ((l.a^r.b)==1 && (l.b^r.a)==1)) )
                return gate(l.a,l.b,true);
        }
        int inv = x ? (a^b)&1 : 0;
        if ( x ) { a &= ~1; b &= ~1; }
        if ( a > b ) std::swap(a,b);
        word key = Key(a,b);
        auto it = gates[x].find(key);
        if ( it != gates[x].end() ) return it->second ^ inv;
        word sa = Phase(nodes[a>>1].sig,a), sb = Phase(nodes[b>>1].sig,b);
        word sig = x ? sa^sb : sa&sb;
        int lit = 2*(int)nodes.size(), phase = (int)(sig&1);
        nodes.push_back({a,b,x,nodes[a>>1].deps | nodes[b>>1].deps,sig});
        vars.push_back(-1);
        if ( index ) {
            auto entry = classes.emplace(Phase(sig,phase), lit^phase);
            if ( !entry.second && sweeping && !expired() ) {
                int other = entry.first->second ^ phase;
                ++checked;
                if ( ask(lit,other^1,80) == GLUCOSE3_UNSAT && ask(lit^1,other,80) == GLUCOSE3_UNSAT )
                    lit = other, ++merged;
            }
        }
        gates[x][key] = lit;
        return lit ^ inv;
    }
    int either( int a, int b ) { return gate(a^1,b^1)^1; }
    int replace( int lit, word mask, const Ints & subs, std::unordered_map<int,int> & memo ) {
        int id = lit>>1;
        Node n = nodes[id];
        if ( !(n.deps & mask) ) return lit;
        if ( n.a < 0 ) return subs[id] ^ (lit&1);
        auto it = memo.find(id);
        if ( it != memo.end() ) return it->second ^ (lit&1);
        int a = replace(n.a,mask,subs,memo);
        int b = replace(n.b,mask,subs,memo);
        int val = gate(a,b,n.isXor);
        memo[id] = val;
        return val ^ (lit&1);
    }
    int disjoin( Ints a ) {
        if ( a.empty() ) return 0;
        while ( a.size() > 1 ) {
            size_t w = 0;
            for ( size_t i = 0; i < a.size(); i += 2 )
                a[w++] = i+1 == a.size() ? a[i] : either(a[i],a[i+1]);
            a.resize(w);
        }
        return a[0];
    }
    void build( Circuit & c, const vector<char> * sweep = NULL ) {
        for ( int id : c.order ) {
            Net & n = c.nets[id];
            if ( sweep ) sweeping = (*sweep)[id];
            if ( n.type == PI || n.type == TARGET ) continue;
            if ( n.type == ZERO || n.type == ONE ) { n.lit = n.type == ONE; continue; }
            int lit = c.nets[n.fanins[0]].lit;
            for ( int j : n.fanins ) n.blocked |= c.nets[j].blocked;
            for ( size_t i = 1; i < n.fanins.size(); ++i ) {
                int b = c.nets[n.fanins[i]].lit;
                if ( n.type == AND || n.type == NAND ) lit = gate(lit,b);
                else if ( n.type == OR || n.type == NOR ) lit = either(lit,b);
                else lit = gate(lit,b,true);
            }
            n.lit = lit ^ (n.type == INV || n.type == NOR || n.type == NAND || n.type == XNOR);
        }
    }
};

const int NoCost = 100000000;
struct Cover {
    int cost = NoCost, net = -1, a = -1, b = -1;
    Gate op = UNDEF;
};

/**Function*************************************************************

  Synopsis    [Maps both phases to legal taps, inverters and two-input cells.]

  Description [The two polarities can select different covers. Shared
  literals are emitted once across all outputs. A direct wire is free.]

***********************************************************************/
struct Map {
    Graph & g;
    const Circuit & f;
    vector<Cover> cover;
    vector<Ints> neighbors;
    Ints distance, rank;
    bool local = false;
    std::unordered_map<int,int> taps;
    // In the reuse pass these gates already have physical wires in the patch.
    std::unordered_set<int> shared;
    Map( Graph & graph, const Circuit & impl, bool pisOnly ) : g(graph), f(impl) {
        neighbors.resize(f.nets.size());
        for ( int i : f.order ) for ( int j : f.nets[i].fanins ) {
            neighbors[i].push_back(j); neighbors[j].push_back(i);
        }
        for ( int i : f.order ) {
            const Net & n = f.nets[i];
            if ( n.blocked || n.weight < 0 || n.lit < 2 || (pisOnly && n.type != PI) ) continue;
            auto it = taps.find(n.lit);
            if ( it == taps.end() || n.weight < f.nets[it->second].weight ) taps[n.lit] = i;
        }
    }
    void focus( int target, bool preferLocal ) {
        local = preferLocal; rank.clear();
        distance.assign(f.nets.size(),1000);
        Ints queue(1,target);
        distance[target] = 0;
        for ( size_t i = 0; i < queue.size(); ++i )
            for ( int j : neighbors[queue[i]] ) if ( distance[j] > distance[queue[i]]+1 ) {
                distance[j] = distance[queue[i]]+1; queue.push_back(j);
            }
    }
    int priority( int lit ) const { return local && lit >= 0 ? rank[lit] : 0; }
    int weight( int lit ) const {
        return shared.count(lit) ? 0 : f.nets[taps.at(lit)].weight;
    }
    void update() {
        for ( int id = (int)cover.size()/2; id < (int)g.nodes.size(); ++id ) {
            Node n = g.nodes[id];
            for ( int p = 0; p < 2; ++p ) {
                int lit = 2*id+p; Cover c;
                auto tap = taps.find(lit);
                if ( id == 0 ) c.cost = 0, c.op = p ? ONE : ZERO;
                else if ( shared.count(lit) ) c.cost = 0;
                else if ( tap != taps.end() ) c.cost = 0, c.net = tap->second;
                else {
                    if ( taps.count(lit^1) || shared.count(lit^1) ) c.cost = 1, c.a = lit^1, c.op = INV;
                    if ( n.a >= 0 ) {
                        for ( int flip = 0; flip < (n.isXor ? 4 : 2); ++flip ) {
                            int a = n.a ^ (flip&1), b = n.b ^ (n.isXor ? flip>>1 : flip);
                            int cost = 1 + cover[a].cost + cover[b].cost;
                            if ( cost >= c.cost ) continue;
                            c.cost = cost; c.a = a; c.b = b;
                            if ( n.isXor ) c.op = (p^(flip&1)^(flip>>1)) ? XNOR : XOR;
                            else c.op = flip ? (p ? OR : NOR) : (p ? NAND : AND);
                        }
                    }
                }
                cover.push_back(c);
            }
        }
        if ( local ) {
            for ( int lit = (int)rank.size(); lit < (int)cover.size(); ++lit ) {
                Cover c = cover[lit];
                int d = 0;
                if ( c.net >= 0 ) d = distance[c.net];
                else if ( c.op == INV && c.a == (lit^1) ) d = cover[c.a].net >= 0 ? distance[cover[c.a].net] : 0;
                else if ( c.a >= 0 ) d = std::max(rank[c.a],c.b >= 0 ? rank[c.b] : 0);
                rank.push_back(d);
            }
        }
    }
};

/**Function*************************************************************

  Synopsis    [Simulates random patterns and neighborhoods of SAT witnesses.]

***********************************************************************/
struct Samples {
    Graph & g;
    vector<Words> batches, patterns;
    explicit Samples( Graph & graph ) : g(graph) {}
    void add( bool witness, int k ) {
        Words pi;
        vector<char> model;
        if ( witness && !g.lastFallback ) {
            model.resize(bmcg3_sat_solver_varnum(g.sat));
            int * cube = bmcg3_sat_solver_read_cex(g.sat);
            for ( int i = 1; i <= cube[0]; ++i ) model[cube[i]>>1] = !(cube[i]&1);
        }
        for ( int lit : g.inputs ) {
            word val = g.rng.next();
            if ( witness ) {
                int v = g.vars[lit>>1];
                bool bit;
                if ( g.lastFallback ) {
                    v = g.fallbackVars[lit>>1];
                    bit = v >= 0 && bmcg3_sat_solver_read_cex_varvalue(g.fallback,v);
                } else bit = v >= 0 && model[v];
                word flips = val;
                for ( int j = 0; j < k; ++j ) flips &= g.rng.next();
                val = Phase(flips & ~(word)1, bit);
            } else if ( k == 0 ) val &= ~(word)1;
            else if ( k == 1 ) val |= 1;
            pi.push_back(val);
        }
        patterns.push_back(std::move(pi)); batches.emplace_back();
    }
    void update() {
        for ( size_t w = 0; w < batches.size(); ++w ) {
            Words & v = batches[w];
            int beg = (int)v.size();
            v.resize(g.nodes.size());
            if ( !beg ) {
                for ( size_t j = 0; j < g.inputs.size(); ++j ) v[g.inputs[j]>>1] = patterns[w][j];
                beg = 1+(int)g.inputs.size();
            }
            for ( int i = beg; i < (int)v.size(); ++i ) {
                Node n = g.nodes[i];
                word a = Phase(v[n.a>>1],n.a), b = Phase(v[n.b>>1],n.b);
                v[i] = n.isXor ? a^b : a&b;
            }
        }
    }
    static word value( const Words & v, int lit ) { return Phase(v[lit>>1],lit); }
    bool fits( int lit, int on, int off ) const {
        for ( const Words & v : batches ) {
            word x = value(v,lit);
            if ( (value(v,on)&~x) | (value(v,off)&x) ) return false;
        }
        return true;
    }
    Words table( int lit ) const {
        Words v;
        for ( const Words & batch : batches ) v.push_back(value(batch,lit));
        return v;
    }
};

static int Pop( word w ) { return Abc_TtCountOnes(w); }

/**Function*************************************************************

  Synopsis    [Ranks divisors on the care set and factors a simulated ISF.]

  Description [The existing ABC resubstitution engine uses a private
  manager for each invocation. No sampled solution is accepted as a proof.]

***********************************************************************/
static int Resynthesize( Graph & g, Map & m, const Samples & s, int on, int off, int limit, const Ints * allowed = NULL )
{
    struct Rank { int lit; double score; };
    vector<Rank> ranks;
    Words pos = s.table(on), neg = s.table(off);
    int nPos = 0, nNeg = 0;
    for ( size_t i = 0; i < pos.size(); ++i ) nPos += Pop(pos[i]), nNeg += Pop(neg[i]);
    if ( !nPos || !nNeg ) return !nNeg;
    Ints choices;
    if ( allowed ) choices = *allowed;
    else for ( const auto & tap : m.taps ) choices.push_back(tap.first);
    for ( int lit : choices ) {
        if ( !allowed && (lit&1) && m.taps.count(lit^1) ) continue;
        int p = 0, n = 0;
        for ( size_t i = 0; i < pos.size(); ++i ) {
            word val = Samples::value(s.batches[i],lit);
            p += Pop(pos[i]&val); n += Pop(neg[i]&val);
        }
        if ( (!p && !n) || (p == nPos && n == nNeg) ) continue;
        double score = fabs((double)p/nPos - (double)n/nNeg);
        ranks.push_back({lit,score});
    }
    std::sort(ranks.begin(),ranks.end(),[](const Rank & a, const Rank & b) {
        return a.score != b.score ? a.score > b.score : a.lit < b.lit;
    });
    if ( ranks.size() > 192 ) ranks.resize(192);
    if ( ranks.empty() ) return -1;
    Ints lits = {0,0};
    vector<Words> vals = {neg,pos};
    for ( const Rank & r : ranks ) { lits.push_back(r.lit); vals.push_back(s.table(r.lit)); }
    vector<void *> ptrs;
    for ( Words & v : vals ) ptrs.push_back(v.data());
    Vec_Ptr_t divs = {(int)ptrs.size(), (int)ptrs.size(), ptrs.data()};
    Vec_Int_t * recipe = Gia_ManResubOne(&divs,(int)pos.size(),std::min(limit,48),
        60,0,1,0,0,NULL,3);
    int result = -1;
    if ( Vec_IntSize(recipe) ) {
        for ( int i = 0; i+1 < Vec_IntSize(recipe); i += 2 ) {
            int a = Vec_IntEntry(recipe,i), b = Vec_IntEntry(recipe,i+1);
            lits.push_back(g.gate(lits[a>>1]^(a&1),lits[b>>1]^(b&1),a>b));
        }
        int lit = Vec_IntEntryLast(recipe);
        result = lits[lit>>1] ^ (lit&1);
    }
    Vec_IntFree(recipe);
    return result;
}

/**Function*************************************************************

  Synopsis    [Classifies reusable nets by their ability to distinguish samples.]

  Description [A set of taps is sufficient on the samples when no on-set
  row and off-set row have identical tap values. A hash collision can only
  retain an unnecessary tap. Recursive removal tries whole blocks first.]

***********************************************************************/
struct Relevance {
    Graph & g;
    const Samples & s;
    int on, off;
    Ints rows, labels, pool, priority;
    Words keys, salts;
    vector<Ints> activeRows;
    vector<Words> prefix;
    enum { Block = 32 };
    vector<unsigned> seen;
    Words slots;
    unsigned epoch = 0;
    Relevance( Graph & graph, Map & m, const Samples & sim, int a, int b ) :
        g(graph), s(sim), on(a), off(b) {
        for ( int j = 0; j < (int)s.batches.size(); ++j ) {
            word pos = Samples::value(s.batches[j],on), neg = Samples::value(s.batches[j],off);
            for ( word w = pos|neg; w; w &= w-1 ) {
                int k = Abc_Tt6FirstBit(w); rows.push_back(64*j+k);
                labels.push_back((int)((pos>>k)&1));
            }
        }
        vector<char> cone(g.nodes.size()), inside(g.nodes.size());
        cone[on>>1] = cone[off>>1] = 1;
        for ( int i = (int)cone.size()-1; i > 0; --i ) {
            Node n = g.nodes[i];
            if ( cone[i] && n.a >= 0 ) cone[n.a>>1] = cone[n.b>>1] = 1;
        }
        inside[0] = 1;
        for ( int i = 1; i < (int)inside.size(); ++i ) {
            Node n = g.nodes[i];
            inside[i] = n.a < 0 ? cone[i] : (inside[n.a>>1] && inside[n.b>>1]);
            if ( !inside[i] ) continue;
            int lit = 2*i;
            if ( !m.taps.count(lit) ) ++lit;
            if ( m.taps.count(lit) ) { pool.push_back(lit); priority.push_back(cone[i]); }
        }
        size_t size = 2;
        while ( size < 4*rows.size() ) size *= 2;
        slots.resize(size); seen.resize(size); keys.resize(rows.size());
        for ( size_t j = 0; j < pool.size(); ++j ) salts.push_back(g.rng.next()|1);
    }
    int bit( int lit, int row ) const {
        return (int)((s.batches[row>>6][lit>>1] >> (row&63))&1) ^ (lit&1);
    }
    bool separates() {
        epoch += 2;
        for ( size_t i = 0; i < keys.size(); ++i ) {
            word h = keys[i];
            size_t k = (size_t)(h ^ (h>>32)) & (slots.size()-1);
            while ( seen[k] >= epoch && slots[k] != h ) k = (k+1)&(slots.size()-1);
            unsigned tag = epoch + labels[i];
            if ( seen[k] >= epoch && seen[k] != tag ) return false;
            slots[k] = h; seen[k] = tag;
        }
        return true;
    }
    void toggleTaps( Words & values, const Ints & order, int beg, int end ) const {
        for ( int j = beg; j < end; ++j ) {
            int tap = order[j];
            for ( int row : activeRows[tap] ) values[row] ^= salts[tap];
        }
    }
    void toggle( const Ints & order, int beg, int end ) {
        int left = (beg+Block-1)/Block, right = end/Block;
        if ( left >= right ) { toggleTaps(keys,order,beg,end); return; }
        toggleTaps(keys,order,beg,left*Block);
        for ( size_t i = 0; i < rows.size(); ++i ) keys[i] ^= prefix[left][i] ^ prefix[right][i];
        toggleTaps(keys,order,right*Block,end);
    }
    void remove( const Ints & order, int beg, int end, Ints & keep ) {
        if ( beg == end ) return;
        toggle(order,beg,end);
        if ( separates() ) return;
        toggle(order,beg,end);
        if ( end-beg == 1 ) { keep.push_back(order[beg]); return; }
        int mid = beg+(end-beg)/2;
        remove(order,beg,mid,keep); remove(order,mid,end,keep);
    }
    Ints support( const Ints & order ) {
        // A recursive removal toggles contiguous ranges repeatedly. Block
        // prefixes update a whole range with two XORs per sample.
        prefix.resize(order.size()/Block+1);
        prefix[0].assign(rows.size(),0);
        for ( int b = 1; b < (int)prefix.size(); ++b ) {
            prefix[b] = prefix[b-1];
            toggleTaps(prefix[b],order,(b-1)*Block,b*Block);
        }
        keys = prefix.back();
        toggleTaps(keys,order,((int)prefix.size()-1)*Block,(int)order.size());
        Ints keep;
        if ( separates() ) remove(order,0,(int)order.size(),keep);
        return keep;
    }
    int factor( const Ints & sel ) {
        int n = (int)sel.size();
        if ( !n || n > 14 ) return -1;
        vector<unsigned> truth[2];
        for ( auto & v : truth ) v.resize(Kit_TruthWordNum(n));
        for ( size_t i = 0; i < rows.size(); ++i ) {
            unsigned sig = 0;
            for ( int j = 0; j < n; ++j ) sig |= (unsigned)bit(pool[sel[j]],rows[i])<<j;
            truth[labels[i]][sig>>5] |= 1u<<(sig&31);
        }
        for ( size_t i = 0; i < truth[0].size(); ++i ) if ( truth[0][i] & truth[1][i] ) return -1;
        if ( n < 5 ) for ( auto & v : truth ) for ( int k = n; k < 5; ++k ) v[0] |= v[0] << (1<<k);
        Vec_Int_t * mem = Vec_IntAlloc(0);
        Kit_Graph_t * dec = Kit_TruthToGraph2(truth[0].data(),truth[1].data(),n,mem);
        Vec_IntFree(mem);
        if ( !dec ) return -1;
        int res;
        if ( Kit_GraphIsConst(dec) ) res = Kit_GraphIsConst1(dec);
        else {
            Ints lits;
            for ( int j : sel ) lits.push_back(pool[j]);
            Kit_Node_t * node; int i;
            Kit_GraphForEachNode(dec,node,i)
                lits.push_back(g.gate(lits[node->eEdge0.Node]^node->eEdge0.fCompl,
                                      lits[node->eEdge1.Node]^node->eEdge1.fCompl));
            res = lits[dec->eRoot.Node] ^ Kit_GraphIsComplement(dec);
        }
        Kit_GraphFree(dec);
        return res;
    }
    void candidates( Map & m, int & best, int & cost ) {
        if ( pool.empty() || rows.empty() ) return;
        // Deduplicate identical sample columns. Rank the duplicates by
        // proximity to the care cones, then by topological order.
        Ints order;
        std::unordered_map<word,int> columns;
        for ( int k = 0; k < (int)pool.size(); ++k ) {
            word h = 0;
            for ( const Words & v : s.batches ) {
                word care = Samples::value(v,on) | Samples::value(v,off);
                h = (h ^ (Samples::value(v,pool[k])&care)) * ABC_CONST(0x9e3779b185ebca87);
            }
            auto r = columns.emplace(h,k);
            if ( !r.second && priority[k] >= priority[r.first->second] ) r.first->second = k;
        }
        for ( auto & v : columns ) order.push_back(v.second);
        std::sort(order.begin(),order.end(),[this](int a,int b) {
            return priority[a] != priority[b] ? priority[a] < priority[b] : a<b;
        });
        // Portions far from the target can contain thousands of unrelated taps.
        if ( order.size() > 1600 ) order.erase(order.begin(),order.end()-1600);
        activeRows.assign(pool.size(),{});
        for ( int k : order )
            for ( int i = 0; i < (int)rows.size(); ++i )
                if ( bit(pool[k],rows[i]) ) activeRows[k].push_back(i);
        for ( int run = 0; run < 4 && cost > 1 && !g.expired(); ++run ) {
            if ( run == 1 ) std::reverse(order.begin(),order.end());
            if ( run >= 2 )
                for ( int i = (int)order.size()-1; i > 0; --i ) std::swap(order[i],order[g.rng.next()%(i+1)]);
            Ints keep = support(order);
            if ( keep.empty() ) continue;
            int cand = factor(keep);
            m.update();
            if ( cand >= 0 && m.cover[cand].cost < cost ) best = cand, cost = m.cover[cand].cost;
        }
    }
};

/**Function*************************************************************

  Synopsis    [Proves a sufficient set of taps with a two-copy SAT query.]

  Description [One copy must be in the on-set and the other in the
  off-set. An unsatisfiable core of tap equalities therefore implements
  functional dependence even on unobserved, rare input patterns.]

***********************************************************************/
struct Depend {
    Graph & src;
    Graph pair;
    Ints copies[2];
    Ints equal, core;
    int care[2], last = GLUCOSE3_UNDEC;
    Depend( Graph & g, const Relevance & rel ) : src(g), pair(g.deadline,false) {
        pair.index = false;
        for ( auto & map : copies ) map.resize(g.nodes.size(),-1);
        care[0] = copy(rel.on,0); care[1] = copy(rel.off,1);
        for ( int lit : rel.pool ) equal.push_back(pair.gate(copy(lit,0),copy(lit,1),true)^1);
    }
    int copy( int lit, int side ) {
        int id = lit>>1;
        int & r = copies[side][id];
        if ( r < 0 ) {
            Node n = src.nodes[id];
            if ( !id ) r = 0;
            else if ( n.a < 0 ) r = pair.input(0);
            else {
                int a = copy(n.a,side), b = copy(n.b,side);
                r = pair.gate(a,b,n.isXor);
            }
        }
        return r^(lit&1);
    }
    bool sufficient( const Ints & supp, int budget ) {
        if ( pair.expired() ) return false;
        Ints lits = {pair.satLit(care[0]),pair.satLit(care[1])};
        std::unordered_map<int,int> indices;
        for ( int k : supp ) {
            int lit = pair.satLit(equal[k]);
            indices[lit>>1] = k; lits.push_back(lit);
        }
        bmcg3_sat_solver_set_conflict_budget(pair.sat,budget);
        last = bmcg3_sat_solver_solve(pair.sat,lits.data(),(int)lits.size());
        if ( last != GLUCOSE3_UNSAT ) return false;
        int * finalLits;
        int n = bmcg3_sat_solver_final(pair.sat,&finalLits);
        core.clear();
        for ( int i = 0; i < n; ++i ) {
            auto it = indices.find(finalLits[i]>>1);
            if ( it != indices.end() ) core.push_back(it->second);
        }
        std::sort(core.begin(),core.end());
        return true;
    }
    // On-set/off-set witness pairs distinguish whole classes of supports.
    // A hitting set of their differences becomes the next dependence query.
    Ints discover( const Relevance & rel, const Map & m ) {
        vector<Words> diff(rel.pool.size());
        Ints best, active;
        int np = 0;
        for ( int iter = 0; iter < 80 && !pair.expired(); ++iter ) {
            if ( sufficient(active,350) ) return minimize(active);
            // A bounded query can be undecided. Only a SAT model is a witness.
            if ( last != GLUCOSE3_SAT ) break;
            Words values(src.nodes.size());
            for ( int lit : src.inputs ) {
                int id = lit>>1;
                for ( int side = 0; side < 2; ++side ) {
                    int copyLit = copies[side][id];
                    if ( copyLit < 0 || pair.vars[copyLit>>1] < 0 ) continue;
                    int value = bmcg3_sat_solver_read_cex_varvalue(pair.sat,pair.vars[copyLit>>1])^(copyLit&1);
                    values[id] |= (word)value<<side;
                }
            }
            for ( size_t k = 1+src.inputs.size(); k < values.size(); ++k ) {
                Node n = src.nodes[k];
                word a = Phase(values[n.a>>1],n.a), b = Phase(values[n.b>>1],n.b);
                values[k] = n.isXor ? a^b : a&b;
            }
            if ( !(Samples::value(values,rel.on)&1) || !(Samples::value(values,rel.off)&2) ) break;
            int changes = 0;
            for ( size_t j = 0; j < rel.pool.size(); ++j ) {
                if ( !(np&63) ) diff[j].push_back(0);
                word v = values[rel.pool[j]>>1];
                if ( (v^(v>>1))&1 ) { diff[j].back() |= (word)1<<(np&63); ++changes; }
            }
            if ( !changes ) break;
            ++np;
            Words need((np+63)/64,~(word)0);
            if ( np&63 ) need.back() = ((word)1<<(np&63))-1;
            active.clear();
            for (;;) {
                int pick = -1, maxHits = 0, weight = INT_MAX;
                for ( int j = 0; j < (int)diff.size(); ++j ) {
                    int hits = 0;
                    for ( size_t w = 0; w < need.size(); ++w ) hits += Pop(need[w]&diff[j][w]);
                    int wgt = m.f.nets[m.taps.at(rel.pool[j])].weight;
                    if ( hits > maxHits || (hits && hits == maxHits && wgt < weight) )
                        pick = j, maxHits = hits, weight = wgt;
                }
                if ( pick < 0 ) break;
                active.push_back(pick);
                for ( size_t w = 0; w < need.size(); ++w ) need[w] &= ~diff[pick][w];
            }
        }
        return best;
    }
    Ints minimize( const Ints & candidates ) {
        if ( !sufficient(candidates,2500) ) return {};
        Ints keep = core, initial = core;
        for ( int drop : initial ) {
            auto it = std::find(keep.begin(),keep.end(),drop);
            if ( it == keep.end() ) continue;
            Ints next = keep;
            next.erase(next.begin()+(it-keep.begin()));
            if ( sufficient(next,400) ) keep = core;
        }
        return keep;
    }
};

/**Function*************************************************************

  Synopsis    [Tries shallow decompositions over the sampled care relation.]

  Description [For an XOR residual, either input polarity is legal. For
  an AND residual, a literal must cover the entire on-set. Searching both
  polarities of the function also covers OR, NAND and NOR decompositions.]

***********************************************************************/
struct Shallow {
    Graph & g;
    Map & m;
    const Samples & samples;
    Ints lits;
    vector<Words> columns;
    int trials = 0;
    Shallow( Graph & graph, Map & map, const Samples & s, const Ints & pool ) :
        g(graph), m(map), samples(s) {
        lits = pool;
        std::stable_sort(lits.begin(),lits.end(),[&](int a,int b) {return m.priority(a)<m.priority(b);});
        for ( int lit : lits ) columns.push_back(samples.table(lit));
    }
    // Factor a literal that covers the on-set. The remaining sum only
    // has to exclude off-set rows on which that literal is true.
    int factoredCover( const Words & pos, const Words & neg, int limit ) {
        int best = -1;
        for ( int f = 0; f < 2; ++f ) {
            const Words & on = f ? neg : pos, & off = f ? pos : neg;
            for ( int a = -1; a < 2*(int)lits.size() && !g.expired(); ++a ) {
                Words avoid = off;
                if ( a >= 0 ) {
                    bool covers = true;
                    for ( size_t w = 0; w < on.size(); ++w ) {
                        word x = Phase(columns[a>>1][w],a);
                        if ( on[w] & ~x ) { covers = false; break; }
                        avoid[w] &= x;
                    }
                    if ( !covers || avoid == off ) continue;
                }
                Ints choices;
                for ( int b = 0; b < 2*(int)lits.size(); ++b ) {
                    bool usable = true;
                    for ( size_t w = 0; w < avoid.size(); ++w )
                        if ( avoid[w] & Phase(columns[b>>1][w],b) ) { usable = false; break; }
                    if ( usable ) choices.push_back(b);
                }
                Words left = on;
                Ints terms;
                for ( int k = 0; k < std::min(limit,8); ++k ) {
                    int top = -1, gain = 0;
                    for ( int b : choices ) {
                        int hits = 0;
                        for ( size_t w = 0; w < left.size(); ++w )
                            hits += Pop(left[w] & Phase(columns[b>>1][w],b));
                        if ( hits > gain ) { top = b; gain = hits; }
                    }
                    if ( top < 0 ) break;
                    terms.push_back(lits[top>>1]^(top&1));
                    word remaining = 0;
                    for ( size_t w = 0; w < left.size(); ++w ) {
                        left[w] &= ~Phase(columns[top>>1][w],top);
                        remaining |= left[w];
                    }
                    if ( remaining ) continue;
                    int sum = g.disjoin(terms);
                    int cand = (a < 0 ? sum : g.gate(lits[a>>1]^(a&1),sum)) ^ f;
                    m.update();
                    if ( m.cover[cand].cost < limit ) best = cand, limit = m.cover[cand].cost;
                    break;
                }
            }
        }
        return best;
    }
    // Enumerate XOR-of-products. A packed, balanced sample rejects most
    // pairs; every surviving expression must match all available samples.
    int parityProduct( const Words & pos, const Words & neg ) {
        Ints rows[2];
        for ( size_t i = 0; i < pos.size(); ++i )
            for ( int p = 0; p < 2; ++p )
                for ( word w = p ? pos[i] : neg[i]; w; w &= w-1 )
                    rows[p].push_back(64*(int)i+Abc_Tt6FirstBit(w));
        if ( rows[0].empty() || rows[1].empty() ) return -1;
        Ints chosen;
        word positive = 0;
        for ( int p = 0; p < 2; ++p ) {
            int n = std::min(32,(int)rows[p].size());
            for ( int j = 0; j < n; ++j ) {
                if ( p ) positive |= (word)1<<chosen.size();
                chosen.push_back(rows[p][(size_t)j*rows[p].size()/n]);
            }
        }
        word care = chosen.size()==64 ? ~(word)0 : ((word)1<<chosen.size())-1;
        Words packed(lits.size());
        for ( size_t k = 0; k < lits.size(); ++k )
            for ( size_t j = 0; j < chosen.size(); ++j )
                packed[k] |= ((columns[k][chosen[j]>>6]>>(chosen[j]&63))&1)<<j;
        for ( int pivot = 0; pivot < (int)lits.size() && !g.expired(); ++pivot ) {
            Words rhs(pos.size()), mask(pos.size());
            for ( size_t w = 0; w < pos.size(); ++w ) {
                mask[w] = pos[w]|neg[w];
                rhs[w] = (pos[w]^columns[pivot][w])&mask[w];
            }
            for ( int phase = 0; phase < 2; ++phase ) {
                word p = Phase(positive^packed[pivot],phase)&care, n = ~p&care;
                Ints unates;
                for ( int j = 0; j < (int)lits.size(); ++j ) for ( int inv = 0; inv < 2; ++inv ) {
                    word col = Phase(packed[j],inv);
                    if ( (p&~col) || !(n&~col) || j==pivot ) continue;
                    bool ok = true;
                    for ( size_t w = 0; w < pos.size(); ++w )
                        if ( mask[w] & Phase(rhs[w],phase) & ~Phase(columns[j][w],inv) ) { ok = false; break; }
                    if ( ok ) unates.push_back(2*j+inv);
                }
                for ( size_t j = 0; j < unates.size(); ++j ) {
                    int a = unates[j];
                    for ( size_t k = 0; k < j; ++k ) {
                        int b = unates[k];
                        if ( n & Phase(packed[a>>1],a) & Phase(packed[b>>1],b) ) continue;
                        bool ok = true;
                        for ( size_t w = 0; w < pos.size(); ++w )
                            if ( mask[w] & ~Phase(rhs[w],phase) & Phase(columns[a>>1][w],a) &
                                 Phase(columns[b>>1][w],b) ) { ok = false; break; }
                        if ( ok ) {
                            int term = g.gate(lits[a>>1]^(a&1),lits[b>>1]^(b&1));
                            return g.gate(lits[pivot],term,true)^phase;
                        }
                    }
                }
            }
        }
        return -1;
    }
    int search( const Words & pos, const Words & neg, int depth ) {
        if ( ++trials > 220 || g.expired() ) return -1;
        int nP = 0, nN = 0;
        for ( size_t i = 0; i < pos.size(); ++i ) nP += Pop(pos[i]), nN += Pop(neg[i]);
        if ( !nP || !nN ) return !nN;
        struct Choice { double score; int index, phase, kind; };
        vector<Choice> choices;
        Ints cover[2];
        for ( int j = 0; j < (int)lits.size(); ++j ) {
            int p = 0, n = 0;
            const Words & col = columns[j];
            for ( size_t i = 0; i < pos.size(); ++i ) p += Pop(pos[i]&col[i]), n += Pop(neg[i]&col[i]);
            if ( (!p && !n) || (p == nP && n == nN) ) continue;
            if ( (p == nP && n == 0) || (p == 0 && n == nN) ) return lits[j] ^ (p==0);
            int cost = m.weight(lits[j]);
            double tie = 1.0e-8/(cost+1.);
            if ( p == nP || !p ) {
                int inv = !p;
                cover[0].push_back(2*j+inv);
                choices.push_back({(double)(inv ? n : nN-n)/nN + tie,j,inv,0});
            }
            if ( n == nN || !n ) {
                int inv = !n;
                cover[1].push_back(2*j+inv);
                choices.push_back({(double)(inv ? p : nP-p)/nP + tie,j,inv,1});
            }
            choices.push_back({fabs((double)p/nP-(double)n/nN)+tie,j,0,2});
        }
        // XOR/XNOR can be looked up by their signatures on the care set.
        std::unordered_map<word,int> signatures;
        for ( int j = 0; j < (int)lits.size(); ++j ) for ( int p = 0; p < 2; ++p ) {
            word h = 0;
            for ( size_t i = 0; i < pos.size(); ++i )
                h = (h ^ (Phase(columns[j][i],p)&(pos[i]|neg[i]))) * ABC_CONST(0x9e3779b185ebca87);
            signatures.emplace(h,2*j+p);
        }
        for ( int j = 0; j < (int)lits.size(); ++j ) {
            word h = 0;
            for ( size_t i = 0; i < pos.size(); ++i )
                h = (h ^ ((columns[j][i]^pos[i])&(pos[i]|neg[i]))) * ABC_CONST(0x9e3779b185ebca87);
            auto it = signatures.find(h);
            if ( it == signatures.end() ) continue;
            int other = it->second;
            bool ok = true;
            for ( size_t i = 0; i < pos.size(); ++i )
                if ( (columns[j][i]^Phase(columns[other>>1][i],other)^pos[i]) & (pos[i]|neg[i]) ) { ok=false; break; }
            if ( ok ) return g.gate(lits[j],lits[other>>1]^(other&1),true);
        }
        for ( int f = 0; f < 2; ++f ) {
            const Words & avoid = f ? pos : neg;
            for ( size_t j = 0; j < cover[f].size(); ++j ) {
                int a = cover[f][j];
                for ( size_t k = 0; k < j; ++k ) {
                    int b = cover[f][k];
                    bool ok = true;
                    for ( size_t w = 0; w < avoid.size(); ++w )
                        if ( avoid[w] & Phase(columns[a>>1][w],a) & Phase(columns[b>>1][w],b) ) { ok = false; break; }
                    if ( ok ) return g.gate(lits[a>>1]^(a&1),lits[b>>1]^(b&1)) ^ f;
                }
            }
        }
        if ( depth <= 1 ) return -1;
        std::stable_sort(choices.begin(),choices.end(),[](const Choice & a,const Choice & b) { return a.score > b.score; });
        int counts[3] = {};
        for ( const Choice & c : choices ) {
            if ( counts[c.kind]++ >= (depth > 2 ? 6 : 16) ) continue;
            Words p(pos), n(neg);
            for ( size_t w = 0; w < p.size(); ++w ) {
                word col = Phase(columns[c.index][w],c.phase);
                if ( c.kind == 0 ) n[w] &= col;
                if ( c.kind == 1 ) p[w] &= col;
                if ( c.kind == 2 ) {
                    p[w] = (pos[w]&~col)|(neg[w]&col);
                    n[w] = (neg[w]&~col)|(pos[w]&col);
                }
            }
            int sub = -1;
            if ( depth == 3 && c.kind != 2 && counts[c.kind] <= 4 )
                sub = parityProduct(p,n);
            if ( sub < 0 ) sub = search(p,n,depth-1);
            if ( sub < 0 ) continue;
            int x = lits[c.index]^c.phase;
            return c.kind == 0 ? g.gate(x,sub) : c.kind == 1 ? g.either(x^1,sub) : g.gate(x,sub,true);
        }
        return -1;
    }
};

/**Function*************************************************************

  Synopsis    [Eliminates sparsely coupled targets first.]

  Description [The reverse reconstruction order gives priority to targets
  constrained by several outputs. Disconnected output cones stay separate.]

***********************************************************************/
static Ints EliminationOrder( const Graph & g, const Ints & constraints, int count )
{
    Words scopes;
    for ( int lit : constraints ) scopes.push_back(g.nodes[lit>>1].deps);
    Ints order;
    word done = 0;
    while ( (int)order.size() < count ) {
        int best = -1, score = INT_MAX;
        word chosen = 0;
        for ( int t = 0; t < count; ++t ) {
            word bit = (word)1<<t, neighbors = 0;
            if ( done & bit ) continue;
            int uses = 0;
            for ( word scope : scopes ) if ( scope&bit ) { neighbors |= scope; ++uses; }
            int cost = 10000*Pop(neighbors) + std::min(uses,9999);
            if ( cost < score ) { score = cost; best = t; chosen = neighbors & ~bit; }
        }
        word bit = (word)1<<best;
        scopes.erase(std::remove_if(scopes.begin(),scopes.end(),[bit](word v){return (v&bit)!=0;}),scopes.end());
        if ( chosen ) scopes.push_back(chosen);
        order.push_back(best); done |= bit;
    }
    return order;
}

struct Bounds { int bit, on, off; };

/**Function*************************************************************

  Synopsis    [Existentially eliminates targets from the joint error relation.]

  Description [Only constraints mentioning the current target are joined.
  If the two cofactors are B0 and B1, B0 AND B1 is exactly the residual
  impossibility condition. B0 and B1 are retained for reconstruction.]

***********************************************************************/
static bool Project( Graph & g, Ints cons, const Ints & tars, const Ints & order, vector<Bounds> & steps, int & residual )
{
    Ints subs(1+g.inputs.size(),-1);
    for ( size_t k = 0; k < order.size(); ++k ) {
        if ( g.expired() ) return false;
        int t = order[k];
        word mask = (word)1 << t;
        Ints cone, keep;
        for ( int lit : cons )
            (g.nodes[lit>>1].deps & mask ? cone : keep).push_back(lit);
        int root = g.disjoin(cone);
        int cofs[2];
        for ( int j = 0; j < 2; ++j ) {
            std::unordered_map<int,int> memo;
            subs[tars[t]>>1] = j;
            cofs[j] = g.replace(root,mask,subs,memo);
        }
        steps.push_back({t,cofs[0],cofs[1]});
        int remain = g.gate(cofs[0],cofs[1]);
        if ( remain ) keep.push_back(remain);
        cons.swap(keep);
    }
    residual = g.disjoin(cons);
    return true;
}

static int FactorCubes( Graph & g, const vector<Ints> & cubes )
{
    if ( cubes.empty() ) return 0;
    std::map<int,int> occurs;
    int pivot = -1, freq = 0;
    for ( const Ints & cube : cubes ) {
        if ( cube.empty() ) return 1;
        for ( int lit : cube ) if ( ++occurs[lit] > freq ) pivot = lit, freq = occurs[lit];
    }
    vector<Ints> yes, no;
    for ( auto cube : cubes ) {
        auto it = std::find(cube.begin(),cube.end(),pivot);
        if ( it == cube.end() ) no.push_back(std::move(cube));
        else { cube.erase(it); yes.push_back(std::move(cube)); }
    }
    int a = FactorCubes(g,yes), b = FactorCubes(g,no);
    return g.either(g.gate(pivot,a),b);
}

/**Function*************************************************************

  Synopsis    [Covers the required on-set with SAT-generalized tap cubes.]

  Description [A witness fixes tap phases. Off-set UNSAT cores discard
  irrelevant literals in bulk and each new cube is blocked in the next
  on-set query. Truncating the cover never yields an accepted patch.]

***********************************************************************/
static int CubeCover( Graph & g, Samples & s, const Ints & pool, int on, int off, int bound )
{
    if ( pool.empty() || pool.size() > 2400 ) return -1;
    vector<Ints> cubes;
    int cover = 0, nlits = 0;
    for ( int k = 0; k < std::min(24,bound+1) && !g.expired(); ++k ) {
        int status = g.ask(on,cover^1,400);
        if ( status == GLUCOSE3_UNSAT ) return FactorCubes(g,cubes);
        if ( status != GLUCOSE3_SAT ) return -1;
        Samples model(g); model.add(true,1); model.update();
        const Words & x = model.batches[0];
        Ints phase;
        for ( int tap : pool ) phase.push_back(tap ^ !(Samples::value(x,tap)&1));
        // Prefer literals that exclude many currently known off-set rows.
        vector<std::pair<int,int>> keys;
        for ( int lit : phase ) {
            int hits = 0;
            for ( const Words & batch : s.batches )
                hits += Pop(Samples::value(batch,off) & ~Samples::value(batch,lit));
            keys.emplace_back(-hits,lit);
        }
        std::stable_sort(keys.begin(),keys.end());
        Ints ordered;
        for ( auto key : keys ) ordered.push_back(key.second);
        Ints cube;
        bool found = false;
        for ( size_t n = std::min<size_t>(32,ordered.size());; n = std::min(ordered.size(),2*n) ) {
            Ints allowed(ordered.begin(),ordered.begin()+n);
            if ( g.implies(off,allowed,cube,300) ) { found = true; break; }
            if ( n == ordered.size() ) break;
        }
        if ( !found ) return -1;
        Ints initial = cube;
        for ( int lit : initial ) {
            auto it = std::find(cube.begin(),cube.end(),lit);
            if ( it == cube.end() ) continue;
            Ints reduced = cube, core;
            reduced.erase(reduced.begin()+(it-cube.begin()));
            if ( g.implies(off,reduced,core,200) ) cube.swap(core);
        }
        int term = 1;
        for ( int lit : cube ) term = g.gate(term,lit);
        cover = g.either(cover,term);
        cubes.push_back(cube);
        nlits += (int)cube.size();
        if ( nlits > 4*bound+8 ) break;
    }
    return -1;
}

static void PatchNodes( const Map & m, int lit, std::set<int> & cells )
{
    Cover c = m.cover[lit];
    if ( c.a < 0 || !cells.insert(lit).second ) return;
    PatchNodes(m,c.a,cells);
    if ( c.b >= 0 ) PatchNodes(m,c.b,cells);
}

static int PatchSize( const Map & m, const Ints & roots )
{
    std::set<int> cells;
    for ( int lit : roots ) PatchNodes(m,lit,cells);
    return (int)cells.size();
}

static int PatchCofactor( Graph & g, const Map & m, int lit, int pivot, int value, std::map<int,int> & memo )
{
    if ( (lit>>1) == (pivot>>1) ) return value^((lit^pivot)&1);
    Cover c = m.cover[lit];
    if ( c.a < 0 ) return lit;
    auto it = memo.find(lit);
    if ( it != memo.end() ) return it->second;
    int a = PatchCofactor(g,m,c.a,pivot,value,memo), res;
    if ( c.op == INV ) res = a^1;
    else {
        int b = PatchCofactor(g,m,c.b,pivot,value,memo);
        if ( c.op == XOR || c.op == XNOR ) res = g.gate(a,b,true)^(c.op==XNOR);
        else if ( c.op == OR || c.op == NOR ) res = g.either(a,b)^(c.op==NOR);
        else res = g.gate(a,b)^(c.op==NAND);
    }
    return memo[lit] = res;
}

/**Function*************************************************************

  Synopsis    [Resubstitutes internal patch gates under their observability care.]

  Description [The care for a gate is derived from both cofactors of the
  emitted patch. A replacement must pass SAT and reduce the actual shared
  cell count before another gate is considered.]

***********************************************************************/
static int Improve( Graph & g, Map & m, Samples & s, int root, int on, int off )
{
    std::set<int> nodes;
    PatchNodes(m,root,nodes);
    if ( nodes.size() < 4 ) return root;
    for ( int pass = 0; pass < 2 && !g.expired(); ++pass ) {
        Ints pivots(nodes.begin(),nodes.end());
        std::stable_sort(pivots.begin(),pivots.end(),[&](int a,int b) {return m.cover[a].cost>m.cover[b].cost;});
        bool changed = false;
        for ( int pivot : pivots ) {
            if ( !nodes.count(pivot) || m.cover[pivot].cost < 2 || g.expired() ) continue;
            int bad[2];
            for ( int k = 0; k < 2; ++k ) {
                std::map<int,int> cache;
                int r = PatchCofactor(g,m,root,pivot,k,cache);
                bad[k] = g.either(g.gate(on,r^1),g.gate(off,r));
            }
            std::set<int> skip;
            for ( int attempt = 0; attempt < 4; ++attempt ) {
                m.update(); s.update();
                int cand = -1, cost = std::min(4,m.cover[pivot].cost);
                for ( int lit = 0; lit < (int)m.cover.size(); ++lit )
                    if ( m.cover[lit].cost < cost && !skip.count(lit) && s.fits(lit,bad[0],bad[1]) ) {
                        cand = lit; cost = m.cover[lit].cost;
                        if ( !cost ) break;
                    }
                if ( cand < 0 ) break;
                skip.insert(cand);
                int status = g.ask(bad[0],cand^1,150);
                if ( status == GLUCOSE3_UNSAT ) status = g.ask(bad[1],cand,150);
                if ( status == GLUCOSE3_SAT ) { s.add(true,2); continue; }
                if ( status != GLUCOSE3_UNSAT ) continue;
                std::map<int,int> cache;
                int updated = PatchCofactor(g,m,root,pivot,cand,cache);
                m.update();
                std::set<int> smaller;
                PatchNodes(m,updated,smaller);
                if ( smaller.size() >= nodes.size() ) continue;
                root = updated; nodes.swap(smaller); changed = true;
                break;
            }
        }
        if ( !changed ) break;
    }
    return root;
}

/**Function*************************************************************

  Synopsis    [Finds a small legal completion of a one-bit care interval.]

***********************************************************************/
static int Learn( Graph & g, Map & m, Samples & s, int on, int off, bool verbose )
{
    vector<Ints> proven;
    bool tried = false;
    std::set<int> rejected;
    for ( int round = 0; !g.expired(); ++round ) {
        m.update(); s.update();
        int best = -1, cost = NoCost;
        for ( int lit = 0; lit < (int)m.cover.size(); ++lit ) {
            int c = m.cover[lit].cost;
            if ( c < NoCost && (c < cost || (c == cost && m.priority(lit)<m.priority(best))) && !rejected.count(lit) && s.fits(lit,on,off) ) { best = lit; cost = c; }
        }
        auto offer = [&](int cand) {
            m.update(); s.update();
            if ( cand >= 0 && (m.cover[cand].cost < cost || (m.cover[cand].cost == cost && m.priority(cand)<m.priority(best))) && !rejected.count(cand) && s.fits(cand,on,off) )
                best = cand, cost = m.cover[cand].cost;
        };
        if ( cost > 1 ) {
            Relevance rel(g,m,s,on,off);
            if ( m.local && !rel.pool.empty() && cost > 1 ) {
                Ints close = rel.pool;
                std::stable_sort(close.begin(),close.end(),[&](int a,int b) {return m.priority(a)<m.priority(b);});
                if ( close.size() > 48 ) close.resize(48);
                Shallow tiny(g,m,s,close);
                offer(tiny.search(s.table(on),s.table(off),3));
            }
            if ( !rel.pool.empty() && rel.pool.size() <= 2400 ) {
                Shallow tiny(g,m,s,rel.pool);
                int cand = cost > 2 ? tiny.parityProduct(s.table(on),s.table(off)) : -1;
                offer(cand);
                cand = tiny.search(s.table(on),s.table(off),cost > 3 ? 3 : cost > 2 ? 2 : 1);
                offer(cand);
            }
            if ( !tried && rel.pool.size() && cost > 2 ) {
                tried = true;
                Depend dep(g,rel);
                Ints order;
                for ( int k = 0; k < (int)rel.pool.size(); ++k ) order.push_back(k);
                std::stable_sort(order.begin(),order.end(),[&](int a,int b) {
                    return m.f.nets[m.taps.at(rel.pool[a])].weight < m.f.nets[m.taps.at(rel.pool[b])].weight;
                });
                auto retain = [&](const Ints & sel) {
                    Ints basis;
                    for ( int k : sel ) basis.push_back(rel.pool[k]);
                    if ( !basis.empty() ) proven.push_back(basis);
                    if ( verbose ) printf("    proof support %d from %d taps\n",(int)basis.size(),(int)order.size());
                };
                if ( order.size() <= 2400 ) retain(dep.discover(rel,m));
                // A cheap prefix often suffices. A second classification
                // can then replace several retained taps with a later net.
                for ( int cut = 32; cut < (int)order.size(); cut *= 2 ) {
                    Ints small(order.begin(),order.begin()+cut);
                    Ints sel = dep.minimize(small);
                    if ( !sel.empty() ) { retain(sel); break; }
                }
                retain(dep.minimize(order));
            }
            for ( const Ints & basis : proven ) {
                Ints sel;
                for ( int lit : basis ) {
                    auto fit = std::lower_bound(rel.pool.begin(),rel.pool.end(),lit);
                    if ( fit != rel.pool.end() && *fit == lit ) sel.push_back((int)(fit-rel.pool.begin()));
                }
                if ( sel.size() != basis.size() ) continue;
                int cand = rel.factor(sel);
                offer(cand);
                if ( cost > 1 ) {
                    cand = Resynthesize(g,m,s,on,off,cost,&basis);
                    offer(cand);
                }
            }
            int proposed = best, bound = cost;
            rel.candidates(m,proposed,bound); offer(proposed);
            if ( cost >= 4 && !rel.pool.empty() && rel.pool.size() <= 384 ) {
                Shallow small(g,m,s,rel.pool);
                offer(small.factoredCover(s.table(on),s.table(off),cost));
            }
        }
        if ( cost > 1 ) {
            int cand = Resynthesize(g,m,s,on,off,cost);
            offer(cand);
        }
        s.update();
        if ( best >= 0 && (!s.fits(best,on,off) || rejected.count(best)) ) best = -1;
        if ( best < 0 || round >= 18 ) {
            // Either interval endpoint is a completion when the projected
            // relation is feasible. Retain it as a finite search fallback.
            int endpoint = m.cover[on].cost < m.cover[off^1].cost ? on : off^1;
            if ( m.cover[endpoint].cost == NoCost ) return -1;
            best = endpoint; cost = m.cover[best].cost;
        }
        int result = g.ask(on,best^1);
        if ( result == GLUCOSE3_UNSAT ) result = g.ask(off,best);
        if ( verbose ) printf("    refinement %d: cost %d, SAT status %d\n",round,cost,result);
        if ( result == GLUCOSE3_UNSAT ) {
            if ( m.cover[best].cost >= 6 ) {
                Relevance rel(g,m,s,on,off);
                int orig = best;
                for ( int phase = 0; phase < 2 && !g.expired(); ++phase ) {
                    int cand = CubeCover(g,s,rel.pool,phase ? off : on,phase ? on : off,std::min(25,m.cover[best].cost));
                    if ( cand >= 0 ) offer(cand^phase);
                }
                if ( best != orig && (g.ask(on,best^1,400) != GLUCOSE3_UNSAT || g.ask(off,best,400) != GLUCOSE3_UNSAT) ) best = orig;
            }
            return Improve(g,m,s,best,on,off);
        }
        if ( result != GLUCOSE3_SAT || round >= 18 ) return -1;
        rejected.insert(best);
        for ( int k = 1; k <= 4; ++k ) s.add(true,k);
    }
    return -1;
}

static string VName( const string & s ) { return !s.empty() && s[0] == '\\' ? s+" " : s; }

struct Options {
    int timeout = 0, seed = 1, rounds = 1;
    bool verbose = false, pisOnly = false, module = false;
    const char * patch = "patch.v", * output = "out.v";
};

// Each output is staged beside its destination. If publishing the second
// file fails, restore the first file from its pre-publication copy.
struct StagedFile {
    std::filesystem::path path, temp;
    explicit StagedFile( const char * name ) : path(name) {}
    ~StagedFile() {
        std::error_code ec;
        if ( !temp.empty() ) std::filesystem::remove(temp,ec);
    }
    bool stage( const string & text ) {
        char * name = NULL;
        int fd = Util_TempFileOpen((path.string()+".eco2-").c_str(),"",&name,0);
        if ( fd < 0 ) return false;
        temp = name; ABC_FREE(name);
#if defined(_WIN32)
        FILE * file = _fdopen(fd,"wb");
        if ( !file ) { _close(fd); return false; }
#else
        FILE * file = fdopen(fd,"wb");
        if ( !file ) { close(fd); return false; }
#endif
        bool ok = fwrite(text.data(),1,text.size(),file)==text.size();
        return fclose(file)==0 && ok;
    }
    bool publish() {
        std::error_code ec;
        std::filesystem::rename(temp,path,ec);
        if ( ec ) return false;
        temp.clear(); return true;
    }
};

static bool WritePair( const Options & opt, const string & patch, const string & design )
{
    StagedFile p(opt.patch), f(opt.output), backup(opt.patch);
    if ( !p.stage(patch) || !f.stage(design) ) return false;
    std::error_code ec;
    // Reserve only the short publication interval, including rollback.
    // Separate ABC frames and processes can synthesize concurrently.
    struct Reservation {
        std::filesystem::path dir;
        bool owns;
        Reservation( const std::filesystem::path & dest, std::error_code & err ) :
            dir(dest.string()+".runeco2-lock"), owns(std::filesystem::create_directory(dir,err)) {}
        ~Reservation() { std::error_code err; if ( owns ) std::filesystem::remove(dir,err); }
    };
    Reservation first(p.path,ec);
    if ( !first.owns ) return false;
    Reservation second(f.path,ec);
    if ( !second.owns ) return false;
    bool existed = std::filesystem::exists(p.path,ec);
    if ( ec ) return false;
    if ( existed ) {
        if ( !backup.stage("") ) return false;
        std::filesystem::copy_file(p.path,backup.temp,std::filesystem::copy_options::overwrite_existing,ec);
        if ( ec ) return false;
    }
    if ( !p.publish() ) return false;
    if ( f.publish() ) return true;
    if ( existed ) {
        if ( !backup.publish() ) {
            Abc_Print(-1,"runeco2: previous patch saved in %s\n",backup.temp.string().c_str());
            backup.temp.clear();
        }
    } else std::filesystem::remove(p.path,ec);
    return false;
}

static bool SameFile( const char * a, const char * b )
{
    namespace fs = std::filesystem;
    std::error_code ec;
    if ( fs::equivalent(a,b,ec) ) return true;
    fs::path x = fs::weakly_canonical(fs::absolute(a,ec),ec);
    if ( ec ) return false;
    fs::path y = fs::weakly_canonical(fs::absolute(b,ec),ec);
#if defined(_WIN32)
    return !ec && _stricmp(x.string().c_str(),y.string().c_str()) == 0;
#else
    return !ec && x == y;
#endif
}

static bool OutputPath( const char * name )
{
    namespace fs = std::filesystem;
    std::error_code ec;
    fs::file_status status = fs::symlink_status(name,ec);
    if ( fs::is_regular_file(status) ) return true;
    if ( status.type() != fs::file_type::not_found ) return false;
    fs::path parent = fs::path(name).parent_path();
    return fs::is_directory(parent.empty() ? fs::path(".") : parent,ec);
}

/**Function*************************************************************

  Synopsis    [Emits a shared patch and instantiates it in the original source.]

***********************************************************************/
struct Writer {
    Map & m;
    std::set<int> used;
    std::set<string> names;
    std::map<int,string> wires, formals;
    struct Cell { Gate op; string output, a, b; };
    vector<Cell> cells;
    vector<string> locals, drivers;
    int count = 0;
    explicit Writer( Map & map ) : m(map), drivers(map.f.targets.size()) {}
    string fresh( string s ) {
        while ( m.f.ids.count(s) || m.f.instances.count(s) || !names.insert(s).second ) s += "_";
        return s;
    }
    string formal( int net ) {
        const string & s = m.f.nets[net].name;
        if ( s[0] == '\\' || s.find('[') == string::npos ) return VName(s);
        auto it = formals.find(net);
        if ( it == formals.end() ) it = formals.emplace(net,fresh("eco_port_"+std::to_string(net))).first;
        return it->second;
    }
    string emit( const Map & map, int lit ) {
        auto it = wires.find(lit);
        if ( it != wires.end() ) return it->second;
        const Cover & c = map.cover[lit];
        if ( lit < 2 ) return lit ? "1'b1" : "1'b0";
        if ( c.net >= 0 ) { used.insert(c.net); return formal(c.net); }
        string a = emit(map,c.a), b;
        if ( c.b >= 0 ) b = emit(map,c.b);
        string name = fresh("eco_" + std::to_string(wires.size()));
        wires[lit] = name; locals.push_back(name);
        cells.push_back({c.op,name,a,b});
        ++count;
        return name;
    }
    static string join( const vector<string> & v ) {
        string s;
        for ( size_t i = 0; i < v.size(); ++i ) { if ( i ) s += ", "; s += v[i]; }
        return s;
    }
    string gates( const vector<string> & outputs, const std::map<string,string> & names ) const {
        auto signal = [&](const string & s) {
            auto it = names.find(s);
            return it == names.end() ? s : it->second;
        };
        std::ostringstream out;
        if ( !locals.empty() ) out << "  wire " << join(locals) << ";\n";
        for ( const Cell & c : cells ) {
            out << "  " << GateName[c.op] << " ( " << c.output << ", " << signal(c.a);
            if ( !c.b.empty() ) out << ", " << signal(c.b);
            out << " );\n";
        }
        for ( size_t i = 0; i < outputs.size(); ++i )
            out << "  assign " << signal(outputs[i]) << " = " << signal(drivers[i]) << ";\n";
        return out.str();
    }
    bool write( const Options & opt, long long & resource ) {
        vector<string> outputs, inputs, actual;
        std::map<string,string> bindings;
        for ( int i : m.f.targets ) {
            outputs.push_back(formal(i)); actual.push_back(VName(m.f.nets[i].name));
            bindings[outputs.back()] = actual.back();
        }
        bool crosses = false;
        for ( int n : used ) {
            inputs.push_back(formal(n)); actual.push_back(VName(m.f.nets[n].name));
            bindings[inputs.back()] = actual.back();
            crosses |= m.f.nets[n].blocked;
            resource += m.f.nets[n].weight;
        }
        vector<string> ports = outputs;
        ports.insert(ports.end(),inputs.begin(),inputs.end());
        string mod = m.f.module == "patch" ? "eco_patch" : "patch";
        std::ostringstream body;
        body << "module " << mod << " ( " << join(ports) << " );\n";
        if ( !outputs.empty() ) body << "  output " << join(outputs) << ";\n";
        if ( !inputs.empty() ) body << "  input " << join(inputs) << ";\n";
        body << gates(outputs,{}) << "endmodule\n";
        string design = m.f.text;
        if ( !outputs.empty() && crosses && !opt.module ) {
            // ABC's hierarchical reader assumes every box output can depend
            // on every box input. Inline an acyclic inter-target connection.
            design.insert(m.f.endmodule,"\n"+gates(outputs,bindings));
        } else if ( !outputs.empty() ) {
            string inst = "\n  " + mod + " " + fresh("eco_inst") + " ( " + join(actual) + " );\n";
            design.insert(m.f.endmodule,inst);
            design += "\n" + body.str();
        }
        return WritePair(opt,body.str(),design);
    }
};

/**Function*************************************************************

  Synopsis    [Reuses implementation gates whose upstream repairs are fixed.]

  Description [Implementation nets become available after their upstream
  repairs are emitted. Previously emitted patch gates are also free divisors.
  Up to four targets, all orders are explored and common prefixes are built
  once. Larger patches use two size orders. Only complete, verified patches
  can replace the incumbent.]

***********************************************************************/
struct Reuse {
    Graph & g;
    Map & base;
    const Circuit & f;
    const Ints & targets;
    word all;
    Map map;
    Words dependencies;
    Ints sizes, order, donors, errors;
    Reuse( Graph & graph, Map & m, const Ints & tars, const Ints & constraints,
           word mask, const Ints & patch, bool pisOnly ) : g(graph), base(m), f(m.f), targets(tars),
        all(mask), map(graph,m.f,pisOnly), dependencies(f.nets.size()) {
        for ( int t = 0; t < (int)targets.size(); ++t ) {
            word bit = (word)1 << t;
            dependencies[f.targets[t]] = bit;
            sizes.push_back(PatchSize(base,{patch[t]}));
            order.push_back(t);
            Ints cone;
            for ( int con : constraints ) if ( g.nodes[con>>1].deps & bit ) cone.push_back(con);
            errors.push_back(g.disjoin(cone));
        }
        for ( int i : f.order ) {
            const Net & n = f.nets[i];
            for ( int fan : n.fanins ) dependencies[i] |= dependencies[fan];
            if ( !pisOnly && dependencies[i] && n.weight >= 0 && n.type != TARGET ) donors.push_back(i);
        }
        // Free drivers expose implementation nets immediately. Large repairs
        // can then supply intermediate gates to the smaller repairs.
        std::stable_sort(order.begin(),order.end(),[&](int a,int b) {return sizes[a] < sizes[b];});
        auto first = std::find_if(order.begin(),order.end(),[&](int t){return sizes[t] > 0;});
        std::reverse(first,order.end());
    }
    void extend( int t, word fixed, Ints & patch, Writer & out ) {
        int root = patch[t];
        if ( !fixed || sizes[t] < 2 || out.wires.count(root) ) {
            out.drivers[t] = out.emit(base,root);
            return;
        }
        Ints subs(1+g.inputs.size(),-1);
        for ( size_t i = 0; i < targets.size(); ++i ) subs[targets[i]>>1] = patch[i];
        map.taps = base.taps;
        map.shared.clear();
        for ( const auto & wire : out.wires ) map.shared.insert(wire.first);
        std::unordered_map<word,Ints> classes;
        std::set<int> cells;
        PatchNodes(base,root,cells);
        for ( int lit : cells ) {
            classes[Phase(g.nodes[lit>>1].sig,lit)].push_back(lit);
            classes[Phase(g.nodes[lit>>1].sig,lit^1)].push_back(lit^1);
        }
        auto addTap = [&](int lit, int net) {
            auto it = map.taps.find(lit);
            if ( lit > 1 && (it == map.taps.end() || f.nets[net].weight < f.nets[it->second].weight) )
                map.taps[lit] = net;
        };
        std::unordered_map<int,int> memo;
        for ( int i : donors ) {
            if ( dependencies[i] & ~fixed ) continue;
            const Net & n = f.nets[i];
            int val = g.replace(n.lit,fixed,subs,memo);
            addTap(val,i);
            auto it = classes.find(Phase(g.nodes[val>>1].sig,val));
            if ( it == classes.end() ) continue;
            for ( int alias : it->second )
                if ( alias != val && g.ask(val,alias^1,100)==GLUCOSE3_UNSAT &&
                     g.ask(val^1,alias,100)==GLUCOSE3_UNSAT ) addTap(alias,i);
        }
        map.cover.clear(); map.focus(f.targets[t],true); map.update();
        if ( (map.taps.size() > base.taps.size() || !map.shared.empty()) && map.cover[root].cost > 2 && !g.expired() ) {
            int bound[2];
            for ( int value = 0; value < 2; ++value ) {
                std::unordered_map<int,int> cache;
                subs[targets[t]>>1] = value;
                bound[value] = g.replace(errors[t],all,subs,cache);
            }
            Samples samples(g);
            for ( int i = 0; i < 6; ++i ) samples.add(false,i);
            Ints close;
            for ( const auto & tap : map.taps ) close.push_back(tap.first);
            for ( int lit : map.shared ) if ( !map.taps.count(lit) ) close.push_back(lit);
            std::sort(close.begin(),close.end(),[&](int a,int b) {
                return map.priority(a) != map.priority(b) ? map.priority(a) < map.priority(b) : a < b;
            });
            if ( close.size() > 160 ) close.resize(160);
            for ( int iter = 0; iter < 6 && !g.expired(); ++iter ) {
                samples.update(); map.update();
                int cand = root, area = map.cover[root].cost;
                for ( int lit = 0; lit < (int)map.cover.size(); ++lit )
                    if ( map.cover[lit].cost < area && samples.fits(lit,bound[0],bound[1]) )
                        cand = lit, area = map.cover[lit].cost;
                if ( area > 1 ) {
                    Shallow small(g,map,samples,close);
                    Words pos = samples.table(bound[0]), neg = samples.table(bound[1]);
                    int x = area > 2 ? small.parityProduct(pos,neg) : -1;
                    if ( x < 0 ) x = small.search(pos,neg,std::min(3,area-1));
                    map.update();
                    if ( x >= 0 && map.cover[x].cost < area ) cand = x;
                }
                if ( cand == root ) break;
                int status = g.ask(bound[0],cand^1,400);
                if ( status == GLUCOSE3_UNSAT ) status = g.ask(bound[1],cand,400);
                if ( status == GLUCOSE3_UNSAT ) { root = cand; break; }
                if ( status != GLUCOSE3_SAT ) break;
                samples.add(true,2);
            }
        }
        out.drivers[t] = out.emit(map,root);
        patch[t] = root;
    }
    template<class Accept>
    void enumerate( word fixed, const Ints & patch, const Writer & prefix, Accept & accept ) {
        for ( int t : order ) {
            word bit = (word)1 << t;
            if ( fixed & bit ) continue;
            if ( g.expired() ) return;
            Ints candidate = patch;
            Writer out(prefix);
            extend(t,fixed,candidate,out);
            if ( g.expired() ) return;
            if ( (fixed | bit) == all ) accept(candidate,out);
            else enumerate(fixed | bit,candidate,out,accept);
        }
    }
    template<class Accept>
    void run( const Ints & patch, Accept & accept ) {
        if ( targets.size() <= 4 ) {
            enumerate(0,patch,Writer(base),accept);
            return;
        }
        for ( int pass = 0; pass < 2; ++pass ) {
            if ( pass ) {
                auto first = std::find_if(order.begin(),order.end(),[&](int t){return sizes[t] > 0;});
                if ( order.end()-first < 2 ) return;
                std::reverse(first,order.end());
            }
            Ints candidate = patch;
            Writer out(base);
            word fixed = 0;
            for ( int t : order ) {
                if ( g.expired() ) return;
                extend(t,fixed,candidate,out);
                fixed |= (word)1 << t;
            }
            if ( !g.expired() ) accept(candidate,out);
        }
    }
};

/**Function*************************************************************

  Synopsis    [Resynthesizes the shared patch over its physical tap boundary.]

  Description [Reimporting the optimized AIG exposes complemented gates,
  XORs and common subexpressions across target outputs. The area comparison
  counts the cells that would actually be emitted.]

***********************************************************************/
struct Optimize {
    Graph & g;
    Map & m;
    Gia_Man_t * aig;
    std::map<int,int> remap;
    Ints inputs;
    Optimize( Graph & graph, Map & map ) : g(graph), m(map), aig(Gia_ManStart(128)) {
        char name[] = "eco_patch";
        aig->pName = Abc_UtilStrsav(name);
        Gia_ManHashAlloc(aig);
    }
    ~Optimize() { Gia_ManStop(aig); }
    int exportLit( int lit ) {
        if ( lit < 2 ) return lit;
        auto it = remap.find(lit);
        if ( it != remap.end() ) return it->second;
        // Physical taps in opposite phases represent one Boolean input.
        it = remap.find(lit^1);
        if ( it != remap.end() ) return it->second^1;
        Cover c = m.cover[lit];
        int r;
        if ( c.net >= 0 ) { r = Gia_ManAppendCi(aig); inputs.push_back(lit); }
        else {
            int a = exportLit(c.a);
            int b = c.b >= 0 ? exportLit(c.b) : 0;
            if ( c.op == INV ) r = a^1;
            else if ( c.op == XOR || c.op == XNOR ) r = Gia_ManHashXor(aig,a,b)^(c.op==XNOR);
            else if ( c.op == OR || c.op == NOR ) r = Gia_ManHashOr(aig,a,b)^(c.op==NOR);
            else r = Gia_ManHashAnd(aig,a,b)^(c.op==NAND);
        }
        remap[lit] = r; return r;
    }
    Ints run( const Ints & patch ) {
        Ints roots;
        for ( int lit : patch ) roots.push_back(exportLit(lit));
        for ( int lit : roots ) Gia_ManAppendCo(aig,lit);
        Gia_ManHashStop(aig);
        if ( !Gia_ManAndNum(aig) ) return patch;
        Gia_Man_t * clean = Gia_ManCleanup(aig);
        Gia_Man_t * opt = Gia_ManCompress2(clean,0,0);
        Gia_ManStop(clean);
        Ints map(Gia_ManObjNum(opt)), res;
        Gia_Obj_t * obj; int i;
        Gia_ManForEachCi(opt,obj,i) map[Gia_ObjId(opt,obj)] = inputs[i];
        Gia_ManForEachAnd(opt,obj,i) {
            int a = map[Gia_ObjFaninId0(obj,i)]^Gia_ObjFaninC0(obj);
            int b = map[Gia_ObjFaninId1(obj,i)]^Gia_ObjFaninC1(obj);
            map[i] = g.gate(a,b);
        }
        Gia_ManForEachCo(opt,obj,i) {
            int lit = Gia_ObjFaninLit0p(opt,obj);
            res.push_back(map[lit>>1]^(lit&1));
        }
        Gia_ManStop(opt);
        m.update();
        return res;
    }
};

static bool Ports( const Circuit & f, const Circuit & gold, const Ints & a, const Ints & b, Ints & paired )
{
    if ( a.size() != b.size() ) return false;
    std::unordered_map<string,int> m;
    for ( int id : b ) m[gold.nets[id].name] = id;
    for ( int id : a ) {
        auto it = m.find(f.nets[id].name);
        if ( it == m.end() ) return false;
        paired.push_back(it->second); m.erase(it);
    }
    return m.empty();
}

/**Function*************************************************************

  Synopsis    [Proves all corresponding output pairs of the closed designs.]

***********************************************************************/
static int Verify( Graph & g, const Ints & a, const Ints & b, word mask, const Ints & subs )
{
    std::unordered_map<int,int> memo;
    Ints roots;
    for ( size_t i = 0; i < a.size(); ++i ) {
        int x = g.replace(a[i],mask,subs,memo), y = g.replace(b[i],mask,subs,memo);
        if ( x == y ) continue;
        if ( x == (y^1) ) return 0;
        roots.push_back(x); roots.push_back(y);
    }
    if ( roots.empty() ) return 1;
    if ( g.expired() ) return -1;
    vector<char> need(g.nodes.size());
    for ( int lit : roots ) need[lit>>1] = 1;
    for ( int i = (int)need.size()-1; i > 0; --i ) if ( need[i] && g.nodes[i].a >= 0 ) {
        need[g.nodes[i].a>>1] = need[g.nodes[i].b>>1] = 1;
    }
    Gia_Man_t * aig = Gia_ManStart((int)g.nodes.size()+16);
    char name[] = "runeco2";
    aig->pName = Abc_UtilStrsav(name);
    Gia_ManHashAlloc(aig);
    Ints remap(g.nodes.size());
    for ( int i = 1; i < (int)need.size(); ++i ) if ( need[i] ) {
        Node n = g.nodes[i];
        if ( n.a < 0 ) remap[i] = Gia_ManAppendCi(aig);
        else {
            int x = remap[n.a>>1]^(n.a&1), y = remap[n.b>>1]^(n.b&1);
            remap[i] = n.isXor ? Gia_ManHashXor(aig,x,y) : Gia_ManHashAnd(aig,x,y);
        }
    }
    for ( int lit : roots ) Gia_ManAppendCo(aig,remap[lit>>1]^(lit&1));
    Gia_ManHashStop(aig);
    Cec_ParCec_t pars;
    Cec_ManCecSetDefaultParams(&pars);
    pars.fSilent = 1;
    pars.nBTLimit = 100;
    Cec_ParLimit_t limits = {};
    limits.TimeToStop = g.deadline;
    int status = Cec_ManVerifyWithLimits(aig,&pars,&limits,NULL);
    Gia_ManStop(aig);
    if ( status >= 0 || g.expired() ) return status;
    for ( size_t i = 0; i < roots.size(); i += 2 ) {
        int res = g.ask(g.gate(roots[i],roots[i+1],true));
        if ( res != GLUCOSE3_UNSAT ) return res == GLUCOSE3_SAT ? 0 : -1;
    }
    return 1;
}

static int Error( const string & s ) { Abc_Print(-1,"runeco2: %s\n",s.c_str()); return 1; }

/**Function*************************************************************

  Synopsis    [Computes, checks and writes a complete combinational repair.]

***********************************************************************/
static int Run( const vector<const char *> & files, const Options & opt )
{
    std::clock_t cpuStart = std::clock();
    abctime start = Abc_Clock();
    abctime deadline = opt.timeout ? start + (abctime)opt.timeout*CLOCKS_PER_SEC : 0;
    Circuit f, gold;
    if ( !f.read(files[0],true) ) return Error(string(files[0])+": "+f.error);
    if ( !gold.read(files[1],false) ) return Error(string(files[1])+": "+gold.error);
    if ( !f.weights(files.size()>2 ? files[2] : NULL) ) return Error(f.error);
    if ( f.targets.size() > 64 ) return Error("at most 64 specified targets are supported");
    Ints piG, poG, tars, cons;
    if ( !Ports(f,gold,f.pis,gold.pis,piG) || !Ports(f,gold,f.posNets,gold.posNets,poG) )
        return Error("primary input or output names differ");
    Graph g(deadline);
    g.rng.state ^= (word)(unsigned)(opt.seed-1);
    for ( size_t i = 0; i < f.pis.size(); ++i )
        f.nets[f.pis[i]].lit = gold.nets[piG[i]].lit = g.input(0);
    for ( size_t i = 0; i < f.targets.size(); ++i ) {
        Net & n = f.nets[f.targets[i]];
        tars.push_back(n.lit = g.input((word)1 << i)); n.blocked = true;
    }
    g.build(f);
    vector<char> near(gold.nets.size());
    for ( size_t i = 0; i < poG.size(); ++i )
        if ( f.nets[f.posNets[i]].blocked ) near[poG[i]] = 1;
    for ( auto it = gold.order.rbegin(); it != gold.order.rend(); ++it )
        if ( near[*it] ) for ( int fan : gold.nets[*it].fanins ) near[fan] = 1;
    g.build(gold,&near);
    g.sweeping = true;
    Ints outF, outG;
    for ( size_t i = 0; i < poG.size(); ++i ) {
        outF.push_back(f.nets[f.posNets[i]].lit); outG.push_back(gold.nets[poG[i]].lit);
        if ( !f.nets[f.posNets[i]].blocked ) continue;
        int diff = g.gate(outF.back(),outG.back(),true);
        if ( diff ) cons.push_back(diff);
    }
    g.sweeping = g.index = false;
    if ( opt.verbose ) printf("Graph: %d nodes, %d differences, %d/%d proved equivalences.\n",
        (int)g.nodes.size(),(int)cons.size(),g.merged,g.checked);
    Map m(g,f,opt.pisOnly);
    Ints order, patch, subs(1+g.inputs.size(),-1);
    order = EliminationOrder(g,cons,(int)tars.size());
    int bestCost = NoCost;
    bool found = false;
    word all = tars.size()==64 ? ~(word)0 : (((word)1<<tars.size())-1);
    Ints affectedF, affectedG;
    for ( size_t i = 0; i < poG.size(); ++i ) if ( f.nets[f.posNets[i]].blocked ) {
        affectedF.push_back(outF[i]); affectedG.push_back(outG[i]);
    }
    auto retain = [&](const Ints & candidate, int area) {
        if ( area >= bestCost ) return;
        for ( size_t i = 0; i < tars.size(); ++i ) subs[tars[i]>>1] = candidate[i];
        if ( Verify(g,found ? affectedF : outF,found ? affectedG : outG,all,subs) == 1 ) {
            found = true; patch = candidate; bestCost = area;
            if ( opt.verbose ) printf("  verified incumbent: %d gates at %.3f sec\n",area,(double)(Abc_Clock()-start)/CLOCKS_PER_SEC);
        }
    };
    for ( int trial = 0; trial < opt.rounds && !g.expired(); ++trial ) {
        if ( trial == 1 ) std::reverse(order.begin(),order.end());
        if ( trial > 1 ) for ( int k = (int)order.size()-1; k > 0; --k ) std::swap(order[k],order[g.rng.next()%(k+1)]);
        vector<Bounds> steps;
        int residual;
        if ( !Project(g,cons,tars,order,steps,residual) ) break;
        if ( !trial && g.ask(residual,1,1000) == GLUCOSE3_SAT )
            return Error("no repair exists for the specified targets");
        Samples samples(g);
        for ( int i = 0; i < 12; ++i ) samples.add(false,i);
        Ints attempt(steps.size());
        word mask = 0;
        bool complete = true;
        for ( auto it = steps.rbegin(); it != steps.rend(); ++it ) {
            std::unordered_map<int,int> memo;
            int on = g.replace(it->on,mask,subs,memo);
            int off = g.replace(it->off,mask,subs,memo);
            m.focus(f.targets[it->bit],trial != 1);
            int lit = Learn(g,m,samples,on,off,opt.verbose);
            if ( lit < 0 ) { complete = false; break; }
            attempt[it->bit] = subs[tars[it->bit]>>1] = lit;
            mask |= (word)1 << it->bit;
            if ( opt.verbose ) printf("  target %s: cover cost %d\n",f.nets[f.targets[it->bit]].name.c_str(),m.cover[lit].cost);
        }
        if ( !complete ) continue;
        int area = PatchSize(m,attempt);
        if ( area > 3 ) {
            Optimize optNet(g,m);
            Ints reduced = optNet.run(attempt);
            int reducedArea = PatchSize(m,reduced);
            if ( reducedArea < area ) { attempt.swap(reduced); area = reducedArea; }
        }
        retain(attempt,area);
        if ( bestCost <= 2 || (tars.size()>1 && bestCost <= (int)tars.size()) ) break;
    }
    if ( !found ) return Error(g.expired() ? "time limit reached" : "no verified completion over the legal taps");
    auto chosen = std::make_unique<Writer>(m);
    for ( size_t i = 0; i < patch.size(); ++i ) chosen->drivers[i] = chosen->emit(m,patch[i]);
    if ( tars.size() > 1 && bestCost > 0 && !g.expired() &&
         (tars.size() <= 4 || (!opt.pisOnly && bestCost > 2)) ) {
        int completed = 0;
        auto accept = [&](const Ints & candidate, const Writer & out) {
            ++completed;
            if ( out.count >= chosen->count ) return;
            for ( size_t i = 0; i < tars.size(); ++i ) subs[tars[i]>>1] = candidate[i];
            if ( Verify(g,affectedF,affectedG,all,subs) == 1 ) chosen = std::make_unique<Writer>(out);
        };
        Reuse reuse(g,m,tars,cons,all,patch,opt.pisOnly);
        reuse.run(patch,accept);
        if ( opt.verbose ) printf("  completed %d reuse orders, best patch %d gates\n",completed,chosen->count);
    }
    long long resource = 0;
    if ( !chosen->write(opt,resource) ) return Error("cannot write patch or rectified implementation");
    printf("Verified patch: %d gates, %d taps, weight %lld.  Time = %.3f sec. CPU = %.4f sec\n",
        chosen->count,(int)chosen->used.size(),resource,(double)(Abc_Clock()-start)/CLOCKS_PER_SEC,
        (double)(std::clock()-cpuStart)/CLOCKS_PER_SEC);
    return 0;
}

} // namespace

/**Function*************************************************************

  Synopsis    [Command interface for runeco2.]

***********************************************************************/
int Acb_CommandRunEco2( Abc_Frame_t *, int argc, char ** argv )
{
    Options opt;
    vector<const char *> files;
    for ( int i = 1; i < argc; ++i ) {
        string arg(argv[i]);
        if ( arg == "-h" || arg == "-/" ) goto usage;
        if ( arg == "-T" || arg == "-p" || arg == "-o" || arg == "-S" || arg == "-R" ) {
            if ( ++i >= argc ) goto usage;
            if ( arg == "-p" ) opt.patch = argv[i];
            else if ( arg == "-o" ) opt.output = argv[i];
            else if ( arg == "-S" ) { if ( !Number(argv[i],opt.seed) ) goto usage; }
            else if ( arg == "-R" ) { if ( !Number(argv[i],opt.rounds) || !opt.rounds ) goto usage; }
            else if ( !Number(argv[i],opt.timeout) ) goto usage;
        } else if ( arg == "-v" ) opt.verbose = !opt.verbose;
        else if ( arg == "-i" ) opt.pisOnly = !opt.pisOnly;
        else if ( arg == "-m" ) opt.module = !opt.module;
        else if ( !arg.empty() && arg[0] == '-' ) goto usage;
        else files.push_back(argv[i]);
    }
    if ( files.size() < 2 || files.size() > 3 ) goto usage;
    if ( !OutputPath(opt.patch) || !OutputPath(opt.output) ) return Error("invalid output destination");
    if ( SameFile(opt.patch,opt.output) ) return Error("choose distinct output files");
    for ( const char * file : files )
        if ( SameFile(file,opt.patch) || SameFile(file,opt.output) ) return Error("output would overwrite an input");
    return Run(files,opt);
usage:
    Abc_Print(-2,"usage: runeco2 [-T num] [-S num] [-R num] [-p file] [-o file] [-imvh] <implementation> <specification> [weights]\n");
    Abc_Print(-2,"\t             computes a formally verified combinational ECO patch\n");
    Abc_Print(-2,"\t             tries every gate-reuse order for up to four patch outputs\n");
    Abc_Print(-2,"\t-T <num>   : time limit in seconds (0 = unlimited) [default = 0]\n");
    Abc_Print(-2,"\t-S <num>   : deterministic sampling seed [default = 1]\n");
    Abc_Print(-2,"\t-R <num>   : maximum target order and sampling trials [default = 1]\n");
    Abc_Print(-2,"\t-p <file>  : patch module [default = patch.v]\n");
    Abc_Print(-2,"\t-o <file>  : rectified implementation [default = out.v]\n");
    Abc_Print(-2,"\t-i         : toggle using only primary-input taps [default = no]\n");
    Abc_Print(-2,"\t-m         : toggle always using a patch module instance [default = no]\n");
    Abc_Print(-2,"\t-v         : toggle printing refinement details [default = no]\n");
    Abc_Print(-2,"\t-h         : print the command usage\n");
    Abc_Print(-2,"\timplementation, specification : ICCAD'17 primitive Verilog netlists\n");
    Abc_Print(-2,"\tweights    : eligible implementation nets and their costs [default = all nets, unit cost]\n");
    Abc_Print(-2,"\texample    : runeco2 F.v G.v weight.txt\n");

    Abc_Print(-2,"\n");
    Abc_Print(-2,"\t             The method draws on work by V. N. Kravets and J.-H. R. Jiang.\n");
    Abc_Print(-2,"\t             \"Formalization of Rectification Learning for Economic Design Updates\".\n");
    Abc_Print(-2,"\t             Proc. ASP-DAC 2026, pp. 807-814.\n");
    Abc_Print(-2,"\t             https://doi.org/10.1109/ASP-DAC66049.2026.11420401\n");
    Abc_Print(-2,"\n");
    Abc_Print(-2,"\t             J.-H. R. Jiang, V. N. Kravets, and N.-Z. Lee.\n");
    Abc_Print(-2,"\t             \"Engineering Change Order for Combinational and Sequential\n");
    Abc_Print(-2,"\t             Design Rectification\". Proc. DATE 2020, pp. 726-731.\n");
    Abc_Print(-2,"\t             https://people.eecs.berkeley.edu/~alanmi/publications/other/date20_eco1.pdf\n");
    Abc_Print(-2,"\n");
    Abc_Print(-2,"\t             V. N. Kravets, J.-H. R. Jiang, and H. Riener.\n");
    Abc_Print(-2,"\t             \"Learning to Automate the Design Updates From Observed Engineering\n");
    Abc_Print(-2,"\t             Changes in the Chip Development Cycle\". Proc. DATE 2020, pp. 738-743.\n");
    Abc_Print(-2,"\t             https://people.eecs.berkeley.edu/~alanmi/publications/other/date20_eco2.pdf\n");
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
