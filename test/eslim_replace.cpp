// Regression for replacing an eSLIM window with a larger equivalent circuit.
// Run from the repository root, with assertions enabled in libabc:
// cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug
// cmake --build build --target eslim_replace
// ctest --test-dir build -R '^eslim_replace$' --output-on-failure
#ifdef NDEBUG
#undef NDEBUG
#endif

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <set>
#include <vector>

#include "opt/eslim/eslimCirMan.hpp"
#include "opt/eslim/subcircuit.hpp"

ABC_NAMESPACE_USING_NAMESPACE

// Every gate is reachable, and the output is a & b for any positive size.
static eSLIM::eSLIMCirMan makeCircuit(int gates) {
    eSLIM::eSLIMCirMan circuit(gates + 4);
    int a = circuit.addPi();
    int b = circuit.addPi();
    int output = circuit.addNode({a, b}, 8);
    for (int i = 1; i < gates; ++i)
        output = circuit.addNode({output, i % 2 ? a : b}, 8);
    circuit.addPo(output, false);
    return circuit;
}

static void checkCircuit(const eSLIM::eSLIMCirMan& circuit, int gates) {
    assert(circuit.getNofPis() == 2);
    assert(circuit.getNofPos() == 1);
    assert(circuit.getNofGates() == gates);
    assert(circuit.getNofObjs() == gates + 4);
    assert(circuit.getDepth() == gates + 1);

    std::set<const eSLIM::eSLIMCirObj*> objects;
    std::set<unsigned int> ids;
    for (int i = 0; i < circuit.getNofObjs(); ++i)
        objects.insert(&circuit.getObj(i));
    for (int i = 0; i < circuit.getNofObjs(); ++i) {
        const auto& node = circuit.getObj(i);
        assert(node.node_id == i);
        if (i > 0) {
            bool inserted = ids.insert(node.getId()).second;
            assert(inserted);
        }
        int depth = 0;
        for (auto fanin : node.fanins) {
            assert(objects.count(fanin) == 1);
            assert(fanin->node_id >= 0 && fanin->node_id < i);
            assert(fanin->fanouts.count(const_cast<eSLIM::eSLIMCirObj*>(&node)) == 1);
            depth = std::max(depth, fanin->depth + 1);
        }
        assert(node.depth == depth);
        for (auto fanout : node.fanouts) {
            assert(objects.count(fanout) == 1);
            assert(std::find(fanout->fanins.begin(), fanout->fanins.end(), &node) != fanout->fanins.end());
        }
        if (circuit.isGate(i))
            assert(!node.fanouts.empty());
    }

    // Exhaustively check equivalence to a & b, including the PO truth table.
    for (unsigned input = 0; input < 4; ++input) {
        std::vector<unsigned> values(circuit.getNofObjs(), 0);
        values[1] = input & 1;
        values[2] = (input >> 1) & 1;
        for (int i = 3; i < circuit.getNofObjs(); ++i) {
            const auto& node = circuit.getObj(i);
            unsigned row = 0;
            for (unsigned j = 0; j < node.fanins.size(); ++j)
                row |= values[node.fanins[j]->node_id] << j;
            values[i] = (node.tt >> row) & 1;
        }
        assert(values.back() == (input == 3));
    }
}

int main() {
    auto circuit = makeCircuit(1);
    checkCircuit(circuit, 1);
    // The first replacement grows by two gates: before appending the PO,
    // nodes_aux contains six objects, while the original has only five.
    // Also exercise equal size, growth by one, and shrinking on the same manager.
    for (int gates : {3, 3, 4, 1}) {
        {
            auto replacement = makeCircuit(gates);
            checkCircuit(replacement, gates);
            std::vector<int> nodes;
            for (int i = 3; i < circuit.getNofObjs() - 1; ++i)
                nodes.push_back(i);
            circuit.incrementTraversalId();
            auto subcir = eSLIM::Subcircuit::getSubcircuitBare(circuit, nodes.begin(), nodes.end());
            assert((subcir.inputs == std::vector<int>{1, 2}));
            assert(subcir.outputs.size() == 1);
            circuit.replace(replacement, subcir);
        }
        // Check ownership and links after the replacement manager is destroyed.
        checkCircuit(circuit, gates);
    }
    std::puts("PASS: eSLIM replacement counts, graph consistency and exhaustive equivalence");
}
