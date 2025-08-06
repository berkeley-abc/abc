/**CFile****************************************************************

  FileName    [utilPrefix.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Generating prefix adders.]

  Synopsis    [Generating prefix adders.]

  Author      [Martin Povišer]
  
  Affiliation [<povik@cutebit.org>]

  Date        [Ver. 1.0. Started -August 5, 2025.]

  Revision    [$Id: utilPrefix.cpp,v 1.00 2025/08/05 00:00:00 Exp $]

***********************************************************************/

/*
	The implementation is inspired by S. Roy, M. Choudhury, R. Puri, D. Pan,
	"Polynomial time algorithm for area and power efficient adder synthesis 
	in high-performance designs", Proc. ASP-DAC 2025.

	https://www.cerc.utexas.edu/utda/publications/C166.pdf
*/


#include <algorithm>
#include <list>
#include <iostream>
#include <set>
#include <assert.h>
#include <limits>
#include <vector>
#include <map>
#include <cstdio>


class Graph;
class Node {
public:
	Node(int bitpos, int level=0)
		: level(level), msb(bitpos), lsb(bitpos), pi(true)
	{
	}

	Node(Node *fanin1, Node *fanin2)
		: fanin1(fanin1), fanin2(fanin2)
	{
		assert(fanin1 && fanin2);
		assert(fanin1->lsb == fanin2->msb + 1);
		level = std::max(fanin1->level, fanin2->level) + 1;
		msb = fanin1->msb;
		lsb = fanin2->lsb;
		ref_fanins();
	}

	~Node()
	{
		assert(fanouts.empty());
		deref_fanins();
	}

	Node(const Node&) = delete;
	Node& operator=(const Node&) = delete;
	Node(Node&& other) noexcept {
		fanin1 = other.fanin1;
		fanin2 = other.fanin2;
		level = other.level;
		msb = other.msb;
		lsb = other.lsb;
		other.clear_fanins();
		ref_fanins();
	}

	Node& operator=(Node&& other) noexcept {
		pi = other.pi;
		deref_fanins();
		fanin1 = other.fanin1;
		fanin2 = other.fanin2;
		level = other.level;
		msb = other.msb;
		lsb = other.lsb;
		other.clear_fanins();
		ref_fanins();
		return *this;
	}

	void update_levels() {
		if (!pi)
			level = std::max(fanin1->level, fanin2->level) + 1;
	}

	void update_cap(Graph &graph, bool force=false);

	void clear_fanins() {
		deref_fanins();
		fanin1 = nullptr;
		fanin2 = nullptr;
	}

	int level;
	int level_cap = std::numeric_limits<int>::max();
	std::set<Node *> fanouts;
	int msb, lsb;
	bool pi = false;
	Node *fanin1 = nullptr, *fanin2 = nullptr;

	int node_id;

	int nfanouts() {
		return fanouts.size();
	}

	void deref_fanins() {
		if (fanin1)
			fanin1->fanouts.erase(this);
		if (fanin2)
			fanin2->fanouts.erase(this);
	}

	void ref_fanins() {
		if (fanin1)
			fanin1->fanouts.insert(this);
		if (fanin2)
			fanin2->fanouts.insert(this);
	}
};

class Column {
public:
	Column(int position)
	{
		nodes.emplace_back(position);
	}

	~Column()
	{
		while (!nodes.empty())
			nodes.pop_back();
	}

	Column(const Column&) = delete;
	Column& operator=(const Column&) = delete;

	std::list<Node> nodes;
	int level_constraint;

	void link(Node *fanin2)
	{
		Node *fanin1 = &nodes.back();
		nodes.emplace_back(Node(fanin1, fanin2));
	}

	void link(Column &other)
	{
		Node *fanin1 = &nodes.back();
		Node *fanin2 = &other.nodes.back();
		nodes.emplace_back(Node(fanin1, fanin2));
	}

	bool has_level(int number)
	{
		for (auto &node : nodes)
			if (node.level == number)
				return true;
		return false;
	}

	int no_nodes()
	{
		return (int) nodes.size();
	}

	int level_target = std::numeric_limits<int>::max();
};

struct Graph {
	int bitwidth_;
	int fanout_constraint = std::numeric_limits<int>::max();
	Column **columns;

	~Graph()
	{
		for (int i = bitwidth_ - 1; i >= 0; i--)
			delete columns[i];
		delete[] columns;
	}

	void initialize(int ninputs)
	{
		bitwidth_ = ninputs;
		columns = new Column*[ninputs];
		for (int i = 0; i < ninputs; i++) {
			columns[i] = new Column(i);
		}
	}

	void set_max_fanout(int fanout)
	{
		fanout_constraint = fanout;
	}

	void set_max_depth(int depth)
	{
		for (int i = 0; i < bitwidth(); i++) {
			columns[i]->level_target = depth;
		}
	}

	int bitwidth()
	{
		return bitwidth_;
	}

	Column &operator[](int i)
	{
		return *(columns[i]);
	}

	int min_level()
	{
		int level = std::numeric_limits<int>::max();;
		for (int i = 0; i < bitwidth(); i++)
			level = std::min(level, columns[i]->nodes.front().level);
		return level;
	}

	int max_level()
	{
		int level = std::numeric_limits<int>::min();
		for (int i = 0; i < bitwidth(); i++) {
			level = std::max(level, columns[i]->nodes.back().level);
		}
		return level;
	}

	int size()
	{
		int size = 0;
		for (int i = 0; i < bitwidth(); i++)
			size += columns[i]->nodes.size() - 1;
		return size;
	}

	int max_fanout()
	{
		int max_fanout = 0;
		for (int i = 0; i < bitwidth(); i++) {
			for (auto &node : columns[i]->nodes) {
				max_fanout = std::max(max_fanout, node.nfanouts()); // + (node.lsb == 0));
			}
		}
		return max_fanout;
	}

	bool validate()
	{
		for (int i = 0; i < bitwidth(); i++) {
			if (columns[i]->nodes.back().lsb != 0)
				return false;
		}
		return true;
	}

	void print()
	{
		for (int j = 0; j < bitwidth(); j++)
			for (auto &node : (*this)[j].nodes)
				node.update_levels();

		int min_level1 = min_level();
		int max_level1 = max_level();

		std::cout << "\n" << "size=" << size() \
			<< " max_fanout=" << max_fanout() << " depth=" << max_level1 - min_level1 \
			<< " " << (validate() ? "(validates)" : "") << "\n";

		for (int i = max_level1 + 1; i >= min_level1; i--) {
			std::cout << " ";
			for (int j = bitwidth() - 1; j >= 0; j--) {
				if (i == (*this)[j].nodes.front().level) {
					std::cout << j % 10;
				} else if (i >= (*this)[j].nodes.front().level && i <= (*this)[j].nodes.back().level) {
					if ((*this)[j].has_level(i))
						std::cout << "#";
					else
						std::cout << ".";
				} else if (i - 1 == (*this)[j].level_target) {
					std::cout << "-";
				} else {
					std::cout << " ";
				}
			}
			std::cout << "\n";
		}
	}
};

void Node::update_cap(Graph &graph, bool force) {
	int cap = std::numeric_limits<int>::max();
	if (lsb == 0) {
		cap = std::min(cap, graph.columns[msb]->level_target);
	}
	for (auto fanout : fanouts) {
		cap = std::min(cap, fanout->level_cap - 1);
	}

	if (cap != level_cap || force) {
		level_cap = cap;
		if (fanin1)
			fanin1->update_cap(graph);
		if (fanin2)
			fanin2->update_cap(graph);
	}
}

int ceil_log2(int x)
{
	if (x <= 0)
		return 0;
	x -= 1;
	for (int i = 0;; i++, x >>= 1)
		if (!x)
			return i;
}

void search(Node &node, Graph &graph, std::vector<Node *> &candidate,
			std::vector<Node *> &best, int level_cap, int lsb, int ttl, bool first=false)
{
	if (node.lsb == lsb) {
		/*
		printf("- ");
			for (auto &node : candidate) {
				printf("[%d:%d] ", node->msb, node->lsb);
			}
		printf("\n");
		*/
		if (best.empty() || (candidate.size() <= best.size())) {
			best = candidate;
		}
	} else if ((best.empty() || candidate.size() <= best.size() - 1) && ttl >= 1) {
		auto &nodes = graph.columns[node.lsb - 1]->nodes;
		for (auto it = nodes.rbegin(); it != nodes.rend(); ++it) {
			auto &next_node = *it;
			if ((first || next_node.level > node.level) && next_node.level <= level_cap - 1
					&& next_node.nfanouts() < graph.fanout_constraint && next_node.lsb >= lsb) {
				candidate.push_back(&next_node);
				search(next_node, graph, candidate, best, level_cap, lsb,
						std::min(ttl, level_cap - next_node.level - 1));
				candidate.pop_back();
			}
		}
	}
}

void greedy(Graph &graph, bool algo2=false, bool print=false)
{
	for (int i = graph.bitwidth() - 1; i >= 0; i--)
		graph[i].nodes.back().update_cap(graph);

	for (int i = graph.bitwidth() - 1; i >= 0; i--) {
		Column &column = graph[i];

		for (auto base = std::prev(std::end(column.nodes)); base != std::begin(column.nodes);) {
			auto head = base;

			// find consecutive nodes `base` to `head` within the column which we can replace;
			int prior_area = 1;
			while (!std::prev(base)->pi && std::prev(base)->nfanouts() == 1 \
					&& (!algo2 || !std::prev(std::prev(base))->pi)) {
				base--;
				prior_area++;
			}

			if (prior_area >= 2) {
				std::vector<Node *> candidate, best;
				auto next_head = std::prev(base);

				for (auto it = base; it != std::next(head); it++)
					it->deref_fanins();

				search(*next_head, graph, candidate, best, head->level_cap,
					   head->lsb, std::numeric_limits<int>::max(), true);

				for (auto it = base; it != std::next(head); it++)
					it->ref_fanins();

				std::vector<Node*> old_fanins;
				if (best.size() < static_cast<size_t>(prior_area) && !best.empty()) {
					if (print) {
						printf("(%d) replacing ", i);
						for (auto it = base; it != std::next(head); it++)
							printf("[%d:%d] ", it->fanin2->msb, it->fanin2->lsb);
						printf("with ");
						for (auto node : best)
							printf("[%d:%d] ", node->msb, node->lsb);
						printf("\n");
					}

					// clear the head so that it derefs its fanin1
					old_fanins.push_back(head->fanin2);
					head->clear_fanins();

					// remove all but the head; head will be replaced
					// in place so that its pointer is preserved (it has
					// fanouts)
					auto to_remove = std::prev(head);
					while (to_remove != next_head) {
						auto next = std::prev(to_remove);
						old_fanins.push_back(to_remove->fanin2);
						column.nodes.erase(to_remove);
						to_remove = next;
					}

					// insert replacement nodes
					auto fanin1 = next_head;
					for (auto fanin2 : best) {	
						if (fanin2->lsb == head->lsb) {
							*head = Node(&*fanin1, fanin2);
						} else {
							fanin1 = column.nodes.insert(std::next(fanin1), Node(&*fanin1, fanin2));
						}
					}

					for (auto it = head; it != next_head; it--)
						it->update_cap(graph);
					for (auto old_fanin : old_fanins)
						old_fanin->update_cap(graph);
					for (auto new_fanin : best)
						new_fanin->update_cap(graph);
					next_head->update_cap(graph, true);

					base = next_head;
				} else {
					base--;
				}
			} else {
				base--;
			}
		}
	}

	for (int j = 0; j < graph.bitwidth(); j++)
		for (auto &node : graph[j].nodes)
			node.update_levels();
}

void seed(Graph &graph)
{
	for (int l = 1; l <= ceil_log2(graph.bitwidth()); l++) {
		for (int i = (graph.bitwidth() / 2) * 2 - 1;
			 i >= ((l == 1) ? 3 : ((1 << l) + (1 << (l - 1)) + 1)); i -= 2) {
			graph[i].link(graph[i - (1 << (l - 1))]);
		}
	}

	for (int i = 1; i < (graph.bitwidth() / 2) * 2; i += 2) {
		if (i == 1) {
			graph[i].link(graph[0]);
		} else {
			int base = 1 << (ceil_log2(i) - 1);
			graph[i].link(graph[((i - base) % (base / 2)) + (base / 2)]);
		}
	}
}

// `search2` saves the first candidate of minimal size (compared to `search` which saves the last)
void search2(Node &node, Graph &graph, std::vector<Node *> &candidate,
			std::vector<Node *> &best, int level_cap, int lsb, int ttl, bool first=false)
{
	if (node.lsb == lsb) {
		/*
		printf("- ");
			for (auto &node : candidate) {
				printf("[%d:%d] ", node->msb, node->lsb);
			}
		printf("\n");
		*/
		if (best.empty() || (candidate.size() < best.size())) {
			best = candidate;
		}
	} else if ((best.empty() || candidate.size() < best.size() - 1) && ttl >= 1) {
		auto &nodes = graph.columns[node.lsb - 1]->nodes;
		for (auto it = nodes.rbegin(); it != nodes.rend(); ++it) {
			auto &next_node = *it;
			if ((first || next_node.level > node.level) && next_node.level <= level_cap - 1
					&& next_node.nfanouts() < graph.fanout_constraint && next_node.lsb >= lsb) {
				candidate.push_back(&next_node);
				search2(next_node, graph, candidate, best, level_cap, lsb,
						std::min(ttl, level_cap - next_node.level - 1));
				candidate.pop_back();
			}
		}
	}
}

void algo3(Graph &graph)
{
	for (int i = ((graph.bitwidth() - 1) / 2) * 2; i >= 2; i -= 2) {
		Column &column = graph[i];
		std::vector<Node *> candidate, best;
		search2(column.nodes.back(), graph, candidate, best, column.level_target,
				0, std::numeric_limits<int>::max(), true);
		// if you hit the assert perhaps the fanout constraint was too low
		assert(!best.empty());
		for (auto fanin2 : best) {	
			column.nodes.push_back(Node(&column.nodes.back(), fanin2));
		}
		column.nodes.back().update_cap(graph);
	}

	for (int i = 0; i < graph.bitwidth(); i++)
		for (auto &node : graph[i].nodes)
			node.update_cap(graph);
}

void algo4(Graph &graph)
{
	for (int i = ((graph.bitwidth() - 1) / 2) * 2; i >= 2; i -= 2) {
		Column &column = graph[i];

		if (column.nodes.size() >= 3) {
			Node &node1 = graph[i - 1].nodes.back();
			std::vector<Node *> old_fanins;

			// Try transformation 1
			if (node1.nfanouts() < graph.fanout_constraint
					&& node1.level < column.nodes.back().level_cap) {
				auto head = std::prev(std::end(column.nodes));

				old_fanins.push_back(head->fanin2);
				head->clear_fanins();

				// Remove nodes before their fanins
				auto to_remove = std::prev(head);
				while (to_remove != std::begin(column.nodes)) {
					auto next = std::prev(to_remove);
					old_fanins.push_back(to_remove->fanin2);
					column.nodes.erase(to_remove);
					to_remove = next;
				}

				column.nodes.back() = Node(&column.nodes.front(), &node1);
				column.nodes.back().update_cap(graph, true);
			} else {
				// Try transformation 2
				Node &node2 = graph[i - 2].nodes.back();

				if (node2.nfanouts() < graph.fanout_constraint
						&& graph[i - 1].nodes.front().nfanouts() < graph.fanout_constraint
						&& node2.level < column.nodes.back().level_cap) {

					auto head = std::prev(std::end(column.nodes));
					old_fanins.push_back(head->fanin2);
					head->clear_fanins();

					// Remove nodes before their fanins
					auto to_remove = std::prev(head);
					while (to_remove != std::begin(column.nodes)) {
						auto next = std::prev(to_remove);
						old_fanins.push_back(to_remove->fanin2);
						column.nodes.erase(to_remove);
						to_remove = next;
					}

					auto it = std::prev(std::end(column.nodes));
					column.nodes.insert(it, Node(&column.nodes.front(), &graph[i - 1].nodes.front()));
					column.nodes.back() = Node(&*std::prev(it), &graph[i - 2].nodes.back());
					column.nodes.back().update_cap(graph, true);
				}
			}

			for (auto old_fanin : old_fanins)
				old_fanin->update_cap(graph);
		}
	}
}

// initialize graph with Kogge-Stone
void kogge_stone(Graph &graph)
{
	int width = graph.bitwidth();

	for (int l = 0; l < ceil_log2(width); l++) {
		int stride = 1 << l;
		for (int i = width - 1; i >= stride; i--)
			graph[i].link(graph[i - stride]);
	}
}

// initialize graph with ripple carry
void ripple(Graph &graph)
{
	int width = graph.bitwidth();

	for (int i = 1; i < width; i++) {
		graph[i].link(graph[i - 1]);
	}
}

// Generate complete prefix adder Verilog
void generate_prefix_adder_verilog(Graph& graph, int width, int mfo, int print_miter = 0) 
{
	char filename[100];
	sprintf(filename, "prefix_adder_%d_%d.v", width, mfo);
	FILE *fp = fopen(filename, "w");
	if (!fp) {
		std::cerr << "Error: Cannot create " << filename << std::endl;
		return;
	}
	
	int actual_mfo = graph.max_fanout();
	int size = graph.size();
	// bool valid = graph.validate();  // unused
	
	fprintf(fp, "// Complete Prefix Adder: width=%d, mfo=%d, tree_size=%d\n", width, actual_mfo, size);
	fprintf(fp, "// Generated by C++ version\n");
	fprintf(fp, "module prefix_adder_%d (\n", width);
	fprintf(fp, "  input [%d:0] a,\n", width-1);
	fprintf(fp, "  input [%d:0] b,\n", width-1);
	fprintf(fp, "  output [%d:0] sum\n", width);
	fprintf(fp, ");\n\n");
	
	// Generate propagate and generate signals
	fprintf(fp, "  // Generate propagate (p) and generate (g) signals\n");
	for (int i = 0; i < width; i++) {
		fprintf(fp, "  wire p%d = a[%d] ^ b[%d];\n", i, i, i);
		fprintf(fp, "  wire g%d = a[%d] & b[%d];\n", i, i, i);
	}
	fprintf(fp, "\n");
	
	// Assign unique wire names to all nodes
	// int wire_id = 0;  // unused
	std::map<Node*, std::string> node_to_p_wire;
	std::map<Node*, std::string> node_to_g_wire;
	
	// Assign wire names to input nodes
	for (int i = 0; i < graph.bitwidth(); i++) {
		Node* node = &graph[i].nodes.front();
		char p_name[20], g_name[20];
		sprintf(p_name, "p%d", i);
		sprintf(g_name, "g%d", i);
		node_to_p_wire[node] = p_name;
		node_to_g_wire[node] = g_name;
	}
	
	// Assign wire names to internal nodes
	for (int i = 0; i < graph.bitwidth(); i++) {
		for (auto &node : graph[i].nodes) {
			if (!node.pi) {
				char p_name[20], g_name[20];
				sprintf(p_name, "p_%d_%d", node.msb, node.lsb);
				sprintf(g_name, "g_%d_%d", node.msb, node.lsb);
				node_to_p_wire[&node] = p_name;
				node_to_g_wire[&node] = g_name;
			}
		}
	}
	
	// Generate prefix tree internal nodes using compact prefix cells
	fprintf(fp, "  // Prefix tree computation using traditional prefix cells\n");
	fprintf(fp, "  // Each prefix cell computes:\n");
	fprintf(fp, "  //   p_out = p_in1 & p_in2\n");
	fprintf(fp, "  //   g_out = g_in1 | (p_in1 & g_in2)\n");
	fprintf(fp, "\n");
	
	for (int i = 0; i < graph.bitwidth(); i++) {
		for (auto &node : graph[i].nodes) {
			if (!node.pi) {
				// Generate the propagate output
				fprintf(fp, "  wire %s = %s & %s;\n",
					node_to_p_wire[&node].c_str(),
					node_to_p_wire[node.fanin1].c_str(),
					node_to_p_wire[node.fanin2].c_str());
				
				// Generate the generate output
				fprintf(fp, "  wire %s = %s | (%s & %s); // [%d:%d] = [%d:%d] o [%d:%d]\n",
					node_to_g_wire[&node].c_str(),
					node_to_g_wire[node.fanin1].c_str(),
					node_to_p_wire[node.fanin1].c_str(),
					node_to_g_wire[node.fanin2].c_str(),
					node.msb, node.lsb,
					node.fanin1->msb, node.fanin1->lsb,
					node.fanin2->msb, node.fanin2->lsb);
			}
		}
	}
	fprintf(fp, "\n");
	
	// Extract carry signals from prefix tree
	fprintf(fp, "  // Extract carry signals from prefix tree\n");
	fprintf(fp, "  wire cin = 1'b0; // No carry input\n");
	for (int i = 0; i < graph.bitwidth(); i++) {
		if (graph[i].nodes.back().lsb == 0) {
			fprintf(fp, "  wire c%d = %s; // Carry out of bit %d\n", 
				graph[i].nodes.back().msb, 
				node_to_g_wire[&graph[i].nodes.back()].c_str(), 
				graph[i].nodes.back().msb);
		}
	}
	fprintf(fp, "\n");
	
	// Generate final sum
	fprintf(fp, "  // Compute final sum\n");
	fprintf(fp, "  assign sum[0] = p0 ^ cin;\n");
	for (int i = 1; i < width; i++) {
		fprintf(fp, "  assign sum[%d] = p%d ^ c%d;\n", i, i, i-1);
	}
	fprintf(fp, "  assign sum[%d] = c%d; // Final carry out\n", width, width-1);
	
	fprintf(fp, "\nendmodule\n");
	
	// Generate miter module if requested
	if (print_miter) {
		fprintf(fp, "\n// Miter module for verification\n");
		fprintf(fp, "module prefix_adder_%d_miter (\n", width);
		fprintf(fp, "  input [%d:0] a,\n", width-1);
		fprintf(fp, "  input [%d:0] b,\n", width-1);
		fprintf(fp, "  output miter_output\n");
		fprintf(fp, ");\n\n");
		
		fprintf(fp, "  // Instantiate the prefix adder\n");
		fprintf(fp, "  wire [%d:0] sum_impl;\n", width);
		fprintf(fp, "  prefix_adder_%d adder_inst (\n", width);
		fprintf(fp, "    .a(a),\n");
		fprintf(fp, "    .b(b),\n");
		fprintf(fp, "    .sum(sum_impl)\n");
		fprintf(fp, "  );\n\n");
		
		fprintf(fp, "  // Golden reference using simple addition\n");
		fprintf(fp, "  wire [%d:0] sum_gold = a + b;\n\n", width);
		
		fprintf(fp, "  // Compare outputs - miter_output is 1 if they differ\n");
		fprintf(fp, "  assign miter_output = (sum_gold != sum_impl);\n\n");
		
		fprintf(fp, "endmodule\n");
	}
	
	fclose(fp);
	std::cerr << "Generated complete prefix adder: " << filename << std::endl;
}

// Write variable-length encoded unsigned integer for binary AIGER
void write_aiger_encoded(FILE* fp, unsigned x) {
	unsigned char ch;
	while (x & ~0x7f) {
		ch = (x & 0x7f) | 0x80;
		fputc(ch, fp);
		x >>= 7;
	}
	ch = x;
	fputc(ch, fp);
}

// Create integer array representation of prefix adder AIG
// Returns array in same format as Mini_AigerReadInt, compatible with generate_prefix_adder_aiger_int
extern "C" int* adder_return_array(int width, int mfo, int* pnObjs, int* pnIns, int* pnLatches, int* pnOuts, int* pnAnds, int fDumpVer, int fDumpMiter, int fVerbose) {
	// Build the prefix adder graph
	Graph graph;
	graph.initialize(width);
	graph.set_max_depth(ceil_log2(width));
	graph.set_max_fanout(mfo / 2);
	
	// Build the prefix tree using the same algorithm sequence as main
	seed(graph);
	greedy(graph);
	greedy(graph);
	graph.set_max_fanout(mfo);
	algo3(graph);
	algo4(graph);
	greedy(graph);
	greedy(graph);

	// generate prefix adder with miter
	if ( fDumpVer )
		generate_prefix_adder_verilog(graph, width, mfo, fDumpMiter);
	
	// Count components
	int num_inputs = 2 * width;     // a[0..width-1], b[0..width-1]
	int num_outputs = width + 1;    // sum[0..width]
	int num_latches = 0;            // combinational circuit
	
	// We'll count AND gates as we generate them
	std::vector<std::pair<int, std::pair<int, int>>> and_gates;
	
	// Variable allocation
	int next_var = 2;
	std::map<std::string, int> signal_map;
	
	// Allocate input variables
	for (int i = 0; i < width; i++) {
		signal_map[std::string("a") + std::to_string(i)] = next_var;
		next_var += 2;
	}
	for (int i = 0; i < width; i++) {
		signal_map[std::string("b") + std::to_string(i)] = next_var;
		next_var += 2;
	}
	
	// Generate propagate and generate signals (same as in AIGER generation)
	for (int i = 0; i < width; i++) {
		// pi = ai XOR bi = (ai | bi) & !(ai & bi)
		// First create ai & bi
		int ai = signal_map[std::string("a") + std::to_string(i)];
		int bi = signal_map[std::string("b") + std::to_string(i)];
		
		signal_map[std::string("g") + std::to_string(i)] = next_var;
		and_gates.push_back({next_var, {ai, bi}});
		next_var += 2;
		
		// Create ai | bi = !(!ai & !bi)
		int not_ai_and_not_bi = next_var;
		and_gates.push_back({not_ai_and_not_bi, {ai ^ 1, bi ^ 1}});
		next_var += 2;
		
		// pi = (ai | bi) & !(ai & bi)
		signal_map[std::string("p") + std::to_string(i)] = next_var;
		and_gates.push_back({next_var, {not_ai_and_not_bi ^ 1, signal_map[std::string("g") + std::to_string(i)] ^ 1}});
		next_var += 2;
	}
	
	// Generate prefix tree
	std::map<std::pair<int, int>, std::pair<int, int>> computed_nodes;
	
	for (int i = 0; i < width; i++) {
		computed_nodes[{i, i}] = {
			signal_map[std::string("p") + std::to_string(i)],
			signal_map[std::string("g") + std::to_string(i)]
		};
	}
	
	// Process each node in the graph
	for (int i = 0; i < graph.bitwidth(); i++) {
		for (auto &node : graph[i].nodes) {
			if (node.pi)
				continue;
			
			int msb1 = node.fanin1->msb;
			int lsb1 = node.fanin1->lsb;
			int msb2 = node.fanin2->msb;
			int lsb2 = node.fanin2->lsb;
			
			int p1 = computed_nodes[{msb1, lsb1}].first;
			int g1 = computed_nodes[{msb1, lsb1}].second;
			int p2 = computed_nodes[{msb2, lsb2}].first;
			int g2 = computed_nodes[{msb2, lsb2}].second;
			
			// p_out = p1 & p2
			int p_out = next_var;
			and_gates.push_back({p_out, {p1, p2}});
			next_var += 2;
			
			// g_out = g1 | (p1 & g2)
			int p1_and_g2 = next_var;
			and_gates.push_back({p1_and_g2, {p1, g2}});
			next_var += 2;
			
			// g1 | (p1 & g2) = !(!g1 & !(p1 & g2))
			int g_out = next_var;
			and_gates.push_back({g_out, {g1 ^ 1, p1_and_g2 ^ 1}});
			next_var += 2;
			g_out = g_out ^ 1;
			
			int msb = node.msb;
			int lsb = node.lsb;
			computed_nodes[{msb, lsb}] = {p_out, g_out};
		}
	}
	
	// Generate sum outputs
	std::vector<int> output_signals;
	
	// sum[0] = p0 ^ cin, where cin = 0
	output_signals.push_back(signal_map[std::string("p0")]);
	
	// sum[i] = pi ^ c[i-1] for i = 1 to width-1
	for (int i = 1; i < width; i++) {
		int pi = signal_map[std::string("p") + std::to_string(i)];
		int gi_minus_1 = computed_nodes[{i-1, 0}].second;
		
		// pi XOR gi_minus_1 = (pi | gi_minus_1) & !(pi & gi_minus_1)
		int pi_and_gi = next_var;
		and_gates.push_back({pi_and_gi, {pi, gi_minus_1}});
		next_var += 2;
		
		int not_pi_and_not_gi = next_var;
		and_gates.push_back({not_pi_and_not_gi, {pi ^ 1, gi_minus_1 ^ 1}});
		next_var += 2;
		
		int sum_i = next_var;
		and_gates.push_back({sum_i, {not_pi_and_not_gi ^ 1, pi_and_gi ^ 1}});
		next_var += 2;
		
		output_signals.push_back(sum_i);
	}
	
	// sum[width] = c[width-1] = g[width-1:0]
	output_signals.push_back(computed_nodes[{width-1, 0}].second);
	
	// Now create the integer array in miniaig format
	int nObjs = 1 + num_inputs + 2*num_latches + num_outputs + and_gates.size();
	int* pObjs = (int*)calloc(nObjs * 2, sizeof(int));
	
	// Initialize all entries to NULL (0)
	for (int i = 0; i < nObjs * 2; i++) {
		pObjs[i] = 0;  // MINI_AIG_NULL is typically 0
	}
	
	// Primary inputs don't need initialization beyond NULL
	// Primary outputs
	for (int i = 0; i < num_outputs; i++) {
		pObjs[2*(nObjs-num_outputs-num_latches+i)+0] = output_signals[i];
		pObjs[2*(nObjs-num_outputs-num_latches+i)+1] = 0;  // NULL
	}
	
	// AND gates
	for (size_t i = 0; i < and_gates.size(); i++) {
		int node_lit = and_gates[i].first;
		int lit0 = and_gates[i].second.first;
		int lit1 = and_gates[i].second.second;
		
		// Ensure lit0 < lit1
		if (lit0 > lit1) {
			std::swap(lit0, lit1);
		}
		
		int node_var = node_lit / 2;
		int and_index = node_var - 1 - num_inputs - num_latches;
		
		pObjs[2*(1+num_inputs+num_latches+and_index)+0] = lit0;
		pObjs[2*(1+num_inputs+num_latches+and_index)+1] = lit1;
	}
	
	// Set output parameters
	*pnObjs = nObjs;
	*pnIns = num_inputs;
	*pnLatches = num_latches;
	*pnOuts = num_outputs;
	*pnAnds = and_gates.size();
	
	return pObjs;
}

void generate_prefix_adder_aiger_int( char * pFileName, int * pObjs, int nObjs, int nIns, int nLatches, int nOuts, int nAnds )
{
    FILE * pFile = fopen( pFileName, "wb" ); int i;
    if ( pFile == NULL )
    {
        fprintf( stdout, "generate_prefix_adder_aiger_int(): Cannot open the output file \"%s\".\n", pFileName );
        return;
    }
    fprintf( pFile, "aig %d %d %d %d %d\n", nIns + nLatches + nAnds, nIns, nLatches, nOuts, nAnds );
    for ( i = 0; i < nLatches; i++ )
        fprintf( pFile, "%d\n", pObjs[2*(nObjs-nLatches+i)+0] );
    for ( i = 0; i < nOuts; i++ )
        fprintf( pFile, "%d\n", pObjs[2*(nObjs-nOuts-nLatches+i)+0] );
    for ( i = 0; i < nAnds; i++ )
    {
        int uLit  = 2*(1+nIns+nLatches+i);
        int uLit0 = pObjs[uLit+0];
        int uLit1 = pObjs[uLit+1];
        write_aiger_encoded( pFile, uLit  - uLit1 );
        write_aiger_encoded( pFile, uLit1 - uLit0 );
    }
    fprintf( pFile, "c\n" );
    fclose( pFile );
}
void generate_prefix_adder_aiger( int width, int mfo )
{
	char pFileName[100];
	sprintf( pFileName, "prefix_adder_%d_%d.aig", width, mfo );
	int nObjs = 0, nIns = 0, nLatches = 0, nOuts = 0, nAnds = 0;
	int * pObjs = adder_return_array( width, mfo, &nObjs, &nIns, &nLatches, &nOuts, &nAnds, 0, 0, 0 );
    generate_prefix_adder_aiger_int( pFileName, pObjs, nObjs, nIns, nLatches, nOuts, nAnds );
	printf( "Written prefix adder into AIGER file \"%s\".\n", pFileName );
	free(pObjs);
}

/*
int main(int argc, char const *argv[])
{
	for (auto width : {8, 16, 32, 64, 96, 128}) {
		for (auto mfo : {4, 6, 8, 10, 12, 16, 32}) {
			Graph graph;
			graph.initialize(width);
			graph.set_max_depth(ceil_log2(width));
			graph.set_max_fanout(mfo / 2);
			seed(graph);
			greedy(graph);
			greedy(graph);
			graph.set_max_fanout(mfo);
			algo3(graph);
			algo4(graph);
			greedy(graph);
			greedy(graph);
			
			// Validate the graph
			bool valid = graph.validate();
			int actual_mfo = graph.max_fanout();
			int size = graph.size();
			int depth = graph.max_level() - graph.min_level();
			
			std::cerr << "width=" << graph.bitwidth() << "\tmfo=" << actual_mfo << "\tsize=" << size;
			
			// Add validation status and check constraints
			if (!valid) {
				std::cerr << "\t[INVALID: not all columns reach lsb=0]";
			}
			if (actual_mfo > mfo) {
				std::cerr << "\t[ERROR: max_fanout " << actual_mfo << " exceeds constraint " << mfo << "]";
			}
			if (depth > ceil_log2(width)) {
				std::cerr << "\t[WARNING: depth " << depth << " exceeds target " << ceil_log2(width) << "]";
			}			
			std::cerr << "\n";
			
			// Generate prefix adder with miter for verification
			//generate_prefix_adder_verilog(graph, width, mfo, "cpp_miter", 1);
			
			// Generate AIGER format
			generate_prefix_adder_aiger(width, mfo);
		}
	}
	return 0;
}
*/
