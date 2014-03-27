#include "Player.hh"
#include <vector>
#include <queue>
#include <list>
#include <set>
#include <map>
#include <algorithm>
#include <limits.h>
using namespace std;

// Constants
#define PLAYER_NAME WaitForIt
#define MAX_INT numeric_limits<int>::max()
#define MAX_DOUBLE numeric_limits<double>::max()
#define INF numeric_limits<double>::infinity()
#define STEPS_SIZE 3
#define NICK_RADIUS 16

// Helper structs
struct LEdge {
	int rounds, strength, mushroom, points;
	bool ballsy;
	inline friend bool operator<(const LEdge &a, const LEdge &b) {
		if (a.rounds != b.rounds) return a.rounds < b.rounds;
		if (a.points != b.points) return a.points < b.points;
		if (a.mushroom != b.mushroom) return a.mushroom < b.mushroom;
		return a.strength < b.strength;
	}
};
struct LVertex {
	int id, prev_id, monkey_id, pos, time;
	bool present;
	CType type;
	LEdge edge;
	inline friend bool operator<(const LVertex &a, const LVertex &b) { return a.edge < b.edge; }
};
struct LSteps {
	bool last_frozen, last_alive;
	list<int> steps;
	inline bool update(bool alive, bool frozen, int pos) {  // updates monkey's traks + returns true if the it just died
		bool died = last_alive && !alive;
		if (died) steps.clear();
		last_alive = alive;
		if (!last_alive) return died;
		if (!last_frozen) {
			steps.insert(steps.end(), pos);
			if (int(steps.size()) > STEPS_SIZE) steps.erase(steps.begin());
		}
		last_frozen = frozen;
		return died;
	}
};
struct LPlayerHints { bool beats_me, closing_in, wimp, slow, closest, best_bet, good_idea; };
struct LVertexEval {
	int vertex_id, time_frame;
	bool nick_it, win_it;
	LEdge edge_eval;
	vector<LPlayerHints> rival_monkeys;
	inline friend bool operator<(const LVertexEval &a, const LVertexEval &b) { return a.edge_eval < b.edge_eval; }
};
struct LOptionData {
	LVertex root;
	vector<LVertex> vertices;
	vector<LVertexEval> eval_data;
};
struct LVertexRating {
	bool win_it;
	double rating;
	LVertex vertex;
	inline friend bool operator<(const LVertexRating &a, const LVertexRating &b) {
		if (a.rating < 0.0000001) return false;
		if (a.win_it != b.win_it) return a.win_it;
		return a.rating > b.rating;
	}
};

// Abbreviated types
typedef pair<int, Pos> LDistVertex;
typedef vector<vector<bool> > LPaper;
typedef vector<vector<int> > LDistances;
typedef vector<vector<LVertex> > LGraph;
typedef vector<set<LVertex> > LGoodyz;
typedef vector<LOptionData> LOptions;
typedef vector<LSteps> LPath;

/**
 * Bola De Drac AI: Fizzy cola with a cool lemon aftertaste
 *
 * Proposed solution:
 * Each interest point on the board (monkeys, pods, mushrooms, nuts and balls) is a vertex that is adjacent to all others.
 * Then for each vertex pair there's an edge that represents the path's cost in terms of rounds spent + other stuff like strength, mushroom, etc.
 * This graph is built when appropriate to provide data that is gonna be relevant in decision-making.
 * We can use breadth first search algorithms such as dijkstra to calculate shortest paths.
 * Each able round vertices are awarded points based on the odds of getting there and the need there is for the monkey to actually get there.
 * The estimated number of rounds consumed is used as the denominator to compute each vertex's rating.
 * Long story short, our monkey dashes towards the highest rated vertex :)
 * Note: excuse the squished code, just to avoid going into the 1000+ line source file.
 */
struct PLAYER_NAME : public Player {
	static Player* factory () { return new PLAYER_NAME; }

	// Variables
	Dir dirs[4];
	LPaper paper;
	vector<Pos> ballz, podz;
	LDistances distances;
	LGraph graph;
	LPath paths;
	LVertex next;
	LOptionData options;
	LGoodyz all_ballz, all_podz, all_nutz, all_mushrooms;
	int nut_offset, mushroom_offset, pod_offset, ball_offset, proximity_limit, patience_limit, patience_counter, cheapskate_time,
		real_strength_lower_bound, strength_lower_bound, strength_upper_bound, mushroom_lower_bound;
	LDistances monkey_tracks, likely_moves;
	double default_mult, win_mult, non_win_mult, ball_mult, non_ball_mult, pod_mult, non_pod_mult, nut_mult, non_nut_mult, mushroom_mult, non_mushroom_mult,
		cannon_fodder_mult, threat_mult, bonus_mult, fight_tolerance, null_rating;

	// breadth first search: provides a map of distances for a given position
	void get_distances(Pos p, LPaper scrap, vector<int> &c) {
		c = vector<int>(rows() * cols()); c[p.i * cols() + p.j] = 0; scrap[p.i][p.j] = false;
		queue<LDistVertex> q; q.push(LDistVertex(0, p));
		while (!q.empty()) {
			LDistVertex n = q.front(); q.pop();
			int d = n.first + 1; p = n.second;
			for (int i = 0; i < 4; i++) {
				Pos np = dest(p, dirs[i]);
				if (scrap[np.i][np.j]) { c[np.i * cols() + np.j] = d; scrap[np.i][np.j] = false; q.push(LDistVertex(d, np)); }
			}
		}
	}
	// for new ball spawns
	void find_new_ballz(int n_balls, LPaper scrap) {
		queue<Pos> q;
		for (int i = 0; i < int(ballz.size()); i++) { scrap[ballz[i].i][ballz[i].j] = false; q.push(ballz[i]); }
		for (int i = 0; i < nb_capsules(); i++) { scrap[podz[i].i][podz[i].j] = false; q.push(podz[i]); }
		while (!q.empty()) {
			Pos p = q.front(); q.pop();
			for (int k = 0; k < 4; k++) {
				Pos np = dest(p, dirs[k]);
				if (scrap[np.i][np.j]) {
					if (cell(np).type == Ball) { ballz.push_back(np); if (!--n_balls) return; }
					scrap[np.i][np.j] = false; q.push(np);
				}
			}
		}
	}
	// remove taken balls & find new ones
	void update_ballz() {
		vector<Pos> n_ballz;	// probably a smarter way to handle disappearing balls, still this won't waste much extra time
		for (int i = 0; i < int(ballz.size()); i++) if (cell(ballz[i]).type == Ball) n_ballz.push_back(ballz[i]);
		ballz = n_ballz;
		int b_count = 0;
		for (int i = 0; i < nb_players(); i++) if (goku(i).alive && has_ball(goku(i).type)) b_count++;
		if (int(ballz.size()) + b_count < nb_balls()) {
			find_new_ballz(nb_balls() - (ballz.size() + b_count), paper);
			for (int i = 0; i < int(ballz.size()); i++) if (distances[ballz[i].i * cols() + ballz[i].j].empty())
				get_distances(ballz[i], paper, distances[ballz[i].i * cols() + ballz[i].j]);
		}
	}
	// init random stuff
	void init_vars() {
		dirs[0] = Top; dirs[1] = Bottom; dirs[2] = Left; dirs[3] = Right;
		real_strength_lower_bound = max_strength() * 0.25;
		strength_lower_bound = real_strength_lower_bound < kamehame_penalty() ? kamehame_penalty() : real_strength_lower_bound;
		strength_upper_bound = max_strength() * 0.8;
		mushroom_lower_bound = kinton_life_time() * 0.2;
		cheapskate_time = nb_rounds() - (goku_regen_time() * 0.6);
		proximity_limit = 8;
		patience_limit = kinton_life_time();
		patience_counter = 0;
		next.id = -1;
		nut_offset = 0;
		mushroom_offset = nb_beans();
		pod_offset = mushroom_offset + nb_kintons();
		ball_offset = pod_offset + nb_capsules();
		monkey_tracks = LDistances(nb_players(), vector<int>(ball_offset + nb_balls()));
		paths = LPath(nb_players());
		for (int i = 0; i < nb_players(); i++) { paths[i].last_frozen = false; paths[i].update(true, true, goku(i).pos.i * cols() + goku(i).pos.j); }
	}
	// init legal cells template
	void init_paper() {
		paper = LPaper(rows(), vector<bool>(cols(), true));
		for (int i = 0; i < rows(); i++) for (int j = 0; j < cols(); j++) {
			if (cell(i, j).type == Rock) paper[i][j] = false;
			else if (cell(i, j).type == Capsule) podz.push_back(Pos(i, j));
			else if (cell(i, j).type == Ball) ballz.push_back(Pos(i, j));
		}
	}
	// calculate distance maps for goodies
	void init_distances() {
		distances = LDistances(rows() * cols());
		vector<Magic_Bean> vb = beans(); vector<Kinton_Cloud> vk = kintons();
		for (int i = 0; i < nb_beans(); i++) get_distances(vb[i].pos, paper, distances[vb[i].pos.i * cols() + vb[i].pos.j]);
		for (int i = 0; i < nb_kintons(); i++) get_distances(vk[i].pos, paper, distances[vk[i].pos.i * cols() + vk[i].pos.j]);
		for (int i = 0; i < nb_capsules(); i++) get_distances(podz[i], paper, distances[podz[i].i * cols() + podz[i].j]);
		for (int i = 0; i < nb_balls(); i++) get_distances(ballz[i], paper, distances[ballz[i].i * cols() + ballz[i].j]);
	}
	// prepare the graph
	void init_graph() {
		int n = nb_beans() + nb_kintons() + nb_capsules() + nb_balls();
		graph = LGraph(nb_players(), vector<LVertex>(n));
		vector<Magic_Bean> vb = beans(); vector<Kinton_Cloud> vk = kintons();
		for (int i = 0; i < nb_players(); i++) { int k = 0;
			for (int j = 0; j < nb_beans(); j++, k++) { graph[i][k].type = Bean; graph[i][k].monkey_id = i; graph[i][k].id = k; graph[i][k].pos = vb[j].pos.i * cols() + vb[j].pos.j; }
			for (int j = 0; j < nb_kintons(); j++, k++) { graph[i][k].type = Kinton; graph[i][k].monkey_id = i; graph[i][k].id = k; graph[i][k].pos = vk[j].pos.i * cols() + vk[j].pos.j; }
			for (int j = 0; j < nb_capsules(); j++, k++) { graph[i][k].type = Capsule; graph[i][k].present = true; graph[i][k].monkey_id = i; graph[i][k].id = k; graph[i][k].pos = podz[j].i * cols() + podz[j].j; }
			for (int j = 0; j < nb_balls(); j++, k++) { graph[i][k].type = Ball; graph[i][k].present = true; graph[i][k].monkey_id = i; graph[i][k].id = k; }
		}
	}
	// default multiplier values
	void init_multipliers() {
		default_mult = 1.0;
		win_mult = 2.0;				// winner options count double points :)
		non_win_mult = 1.0;
		ball_mult = 0.0;			// everything is a yes-no choice (1 or 0)
		non_ball_mult = 1.0;
		pod_mult = 1.0;
		non_pod_mult = 0.0;
		nut_mult = 1.0;				// even if unnecessary, nuts & mushrooms have a small multiplier to pick up stuff close to the designated way
		non_nut_mult = 0.0;
		mushroom_mult = 1.5;		// mushrooms can be 50% farther
		non_mushroom_mult = 0.0;
		cannon_fodder_mult = 4.0;   // weak rivals are a worthy waste of time & strong ones suck
		threat_mult = 0.05;
		bonus_mult = 0.5;			// nearby goodies max bonus
		null_rating = 0.0;
		fight_tolerance = 0.9;		// cut them very little slack
	}
	// init all
	void init_all() {
		init_vars();
		init_paper();
		init_distances();
		init_graph();
		init_multipliers();
	}
	// returns # rounds it takes to travel num_steps & cost in strength & kinton
	int get_costly(int num_steps, int &stren, int &kinton_time) {
		int rounds = 0;
		if (kinton_time > 0) {
			if (kinton_time >= num_steps) { kinton_time -= num_steps; return num_steps; }
			else { num_steps -= kinton_time; rounds = kinton_time; kinton_time = 0; }
		}
		int strength_takes = moving_penalty() * num_steps;
		if (stren - strength_takes >= 0) { stren -= strength_takes; return 2 * num_steps + rounds; }
		int medium_steps = stren / moving_penalty(); stren %= moving_penalty(); rounds += 2 * medium_steps; num_steps -= medium_steps;
		return 4 * num_steps + rounds;
	}
	// edge from one vertex to another
	LEdge get_edge(const LVertex &from, const LVertex &to) {
		int strength = from.edge.strength; int mushroom = from.edge.mushroom;
		int rounds = from.edge.rounds + get_costly(distances[to.pos][from.pos], strength, mushroom);
		if (to.time > rounds) rounds = to.time;
		LEdge e; e.rounds = rounds; e.strength = strength; e.mushroom = mushroom; e.ballsy = from.edge.ballsy; e.points = from.edge.points;
		return e;
	}
	// apply vertex type to complete edge value
	void apply_type(const CType &type, LEdge &edge) {
		if (type == Kinton) edge.mushroom += kinton_life_time();
		else if (type == Bean) edge.strength = max_strength();
		else if (type == Capsule && edge.ballsy) {
			edge.ballsy = false;
			edge.points++;
		} else if (type == Ball && !edge.ballsy) edge.ballsy = true;
	}
	void apply_type(LVertex &vertex) { apply_type(vertex.type, vertex.edge); }
	void apply_type(LVertexEval &vertex_eval) { apply_type(graph[0][vertex_eval.vertex_id].type, vertex_eval.edge_eval); }
	// dijkstra returns shortest path in terms of rounds spent
	void shortest_path(int n, vector<bool> &b, vector<LVertex> &vertices) {
		set<LVertex> p_queue;
		for (int i = 0; i < n; i++) if (b[i]) p_queue.insert(vertices[i]);
		while (!p_queue.empty()) {
			LVertex vertex = *p_queue.begin();
			p_queue.erase(p_queue.begin());
			b[vertex.id] = false;
			apply_type(vertex);
			for (int i = 0; i < n; i++) if (b[i]) {
				LEdge e = get_edge(vertex, vertices[i]);
				if (e < vertices[i].edge) {
					p_queue.erase(vertices[i]);
					vertices[i].prev_id = vertex.id;
					vertices[i].edge = e;
					p_queue.insert(vertices[i]);
				}
			}
		}
	}
	// get player vertex
	LVertex get_monkey_vertex(int monkey_id) {
		LVertex v; v.pos = goku(monkey_id).pos.i * cols() + goku(monkey_id).pos.j;
		v.edge.rounds = 0; v.edge.strength = goku(monkey_id).strength; v.edge.mushroom = goku(monkey_id).kinton;
		v.edge.ballsy = has_ball(goku(monkey_id).type); v.edge.points = 0;
		return v;
	}
	// get sorted vertices grouped by type
	set<LVertex> get_vertex_set(const vector<LVertex> &vertices, int offset, int n) {
		set<LVertex> v_set; for (int i = 0; i < n; i++) v_set.insert(vertices[offset + i]); return v_set;
	}
	set<LVertex> get_pod_set(const vector<LVertex> &vertices) { return get_vertex_set(vertices, pod_offset, nb_capsules()); }
	set<LVertex> get_ball_set(const vector<LVertex> &vertices) { return get_vertex_set(vertices, ball_offset, int(ballz.size())); }
	set<LVertex> get_nut_set(const vector<LVertex> &vertices) { return get_vertex_set(vertices, nut_offset, nb_beans()); }
	set<LVertex> get_mushroom_set(const vector<LVertex> &vertices) { return get_vertex_set(vertices, mushroom_offset, nb_kintons()); }
	// prepare vertices for round
	void prepare_vertices() {
		all_ballz = LGoodyz(nb_players()); all_podz = LGoodyz(nb_players());
		all_nutz = LGoodyz(nb_players()); all_mushrooms = LGoodyz(nb_players());
		vector<Magic_Bean> vb = beans(); vector<Kinton_Cloud> vk = kintons();
		for (int i = 0; i < nb_players(); i++) if (goku(i).alive) {
			LVertex v = get_monkey_vertex(i); int k = 0;
			for (int j = 0; j < nb_beans(); j++, k++) {
				graph[i][k].present = vb[j].present; graph[i][k].time = vb[j].time; graph[i][k].prev_id = -1;
				graph[i][k].edge = get_edge(v, graph[i][k]);
			}
			for (int j = 0; j < nb_kintons(); j++, k++) {
				graph[i][k].present = vk[j].present; graph[i][k].time = vk[j].time; graph[i][k].prev_id = -1;
				graph[i][k].edge = get_edge(v, graph[i][k]);
			}
			for (int j = 0; j < nb_capsules(); j++, k++) { graph[i][k].prev_id = -1; graph[i][k].edge = get_edge(v, graph[i][k]); }
			for (int j = 0; j < int(ballz.size()); j++, k++) {
				graph[i][k].prev_id = -1; graph[i][k].pos = ballz[j].i * cols() + ballz[j].j;
				graph[i][k].edge = get_edge(v, graph[i][k]);
			}
			if (i != me()) {  // assume others are smart enough to pick the shortest path... unlike you! XD
				vector<bool> b(k, true); shortest_path(k, b, graph[i]);
				all_ballz[i] = get_ball_set(graph[i]); all_podz[i] = get_pod_set(graph[i]);
				all_nutz[i] = get_nut_set(graph[i]); all_mushrooms[i] = get_mushroom_set(graph[i]);
			}
		}
	}
	// is a monkey going somewhere? -1: not enough data (ie. new born goku); 0: doesn't follow; 1: more or less (ie. stopped for kame); 2: nails it
	int monkey_follows(int monkey_id, int pos) {
		if (paths[monkey_id].steps.size() < STEPS_SIZE) return -1;
		bool follows = true;
		bool nails_it = true;
		int last = MAX_INT;
		for (list<int>::iterator it = paths[monkey_id].steps.begin(); follows && it != paths[monkey_id].steps.end(); it++) {
			if (distances[pos][*it] == last) nails_it = false;
			else if (distances[pos][*it] > last) follows = nails_it = false;
			last = distances[pos][*it];
		}
		if (nails_it) return 2;
		if (follows) return 1;
		return 0;
	}
	// prepare monkey tracking
	void prepare_tracks() {
		int n = ball_offset + ballz.size();
		for (int i = 0; i < nb_players(); i++) if (i != me() && goku(i).alive)
			for (int j = 0; j < n; j++) monkey_tracks[i][j] = monkey_follows(i, graph[me()][j].pos);
	}
	// gather data about traveling from a vertex to its adjacent vertices
	LOptionData get_option_data(int n, const vector<bool> &b, const LVertex &root, const vector<LVertex> &vertices) {
		LOptionData data; data.eval_data = vector<LVertexEval>(n); data.root = root;
		LVertexEval neb; neb.win_it = true; neb.nick_it = false; neb.rival_monkeys = vector<LPlayerHints>(nb_players());
		for (int i = 0; i < n; i++) if (b[i]) {
			LVertexEval ne = neb; ne.vertex_id = i; ne.edge_eval = vertices[i].edge; apply_type(ne);
			set<LVertex> vertex_set; vertex_set.insert(vertices[i]);
			for (int j = 0; j < nb_players(); j++) if (j != me() && goku(j).alive) {
				vertex_set.insert(graph[j][i]);
				if (!(vertices[i].edge < graph[j][i].edge)) { ne.win_it = false; ne.rival_monkeys[j].beats_me = true; }
				ne.rival_monkeys[j].closing_in = monkey_tracks[j][i] == 2 || monkey_tracks[j][i] == 1;
				ne.rival_monkeys[j].wimp = is_wimpy(goku(j).strength);
				ne.rival_monkeys[j].slow = !goku(j).kinton;
				ne.rival_monkeys[j].closest = ne.rival_monkeys[j].good_idea = ne.rival_monkeys[j].best_bet = false;
				if (graph[0][i].type == Ball) {
					if (!ballz.empty()) ne.rival_monkeys[j].closest = all_ballz[j].begin()->id == i;
					if (ne.rival_monkeys[j].closest && !has_ball(goku(j).type))
						{ ne.rival_monkeys[j].good_idea = true; if (ne.rival_monkeys[j].closing_in) ne.rival_monkeys[j].best_bet = true; }
				} else if (graph[0][i].type == Capsule) {
					ne.rival_monkeys[j].closest = all_podz[j].begin()->id == i;
					if (ne.rival_monkeys[j].closest && has_ball(goku(j).type))
						{ ne.rival_monkeys[j].good_idea = true; if (ne.rival_monkeys[j].closing_in) ne.rival_monkeys[j].best_bet = true; }
				} else if (graph[0][i].type == Bean) {
					ne.rival_monkeys[j].closest = all_nutz[j].begin()->id == i;
					if (ne.rival_monkeys[j].closest && ne.rival_monkeys[j].wimp)
						{ ne.rival_monkeys[j].good_idea = true; if (ne.rival_monkeys[j].closing_in) ne.rival_monkeys[j].best_bet = true; }
				} else if (graph[0][i].type == Kinton) {
					ne.rival_monkeys[j].closest = all_mushrooms[j].begin()->id == i;
					if (ne.rival_monkeys[j].closest && ne.rival_monkeys[j].slow)
						{ ne.rival_monkeys[j].good_idea = true; if (ne.rival_monkeys[j].closing_in) ne.rival_monkeys[j].best_bet = true; }
				}
			}
			if (ne.win_it) {
				for (int j = 0; j < nb_players(); j++) if (j != me() && goku(j).alive && ne.rival_monkeys[j].best_bet) ne.nick_it = true;
				set<LVertex>::iterator it = ++(vertex_set.begin());
				ne.time_frame = it == vertex_set.end() ? MAX_INT : it->edge.rounds - vertices[i].edge.rounds; // only player...? dunno how good that is XD
			}
			data.eval_data[i] = ne;
		}
		data.vertices = vertices;
		return data;
	}
	// update each monkey's likeliest next moves
	void likeliest_moves() {
		vector<vector<int> > likeliest(nb_players());
		for (int k = 0; k < nb_players(); k++) if (k != me() && goku(k).alive) {
			int goku_pos = goku(k).pos.i * cols() + goku(k).pos.j;
			if (paths[k].steps.size() > 1) {
				list<int>::iterator it = paths[k].steps.begin();
				int p = *it;
				bool same = true;
				while (++it != paths[k].steps.end() && same) if ((*it) != p) same = false;
				if (same) likeliest[k].push_back(p);
				else {
					vector<int> adjacent;
					for (int i = 0; i < 4; i++) { Pos np = dest(goku(k).pos, dirs[i]); if (paper[np.i][np.j]) adjacent.push_back(np.i * cols() + np.j); }
					for (int i = 0; i < int(options.eval_data.size()); i++) if (options.eval_data[i].rival_monkeys[k].good_idea) {
						int vertex_pos = graph[me()][options.eval_data[i].vertex_id].pos;
						for (int j = 0; j < int(adjacent.size()); j++)
							if (distances[vertex_pos][goku_pos] > distances[vertex_pos][adjacent[j]]) likeliest[k].push_back(adjacent[j]);
					}
				}
			}
		}
		likely_moves = likeliest;
	}
	// cost of traveling to vertices on the board + likeliest
	void prepare_traversal() {
		int n = ball_offset + ballz.size();
		vector<bool> b(n, true);
		LVertex vertex = get_monkey_vertex(me());
		vector<LVertex> vertices = graph[me()];
		options = get_option_data(n, b, vertex, vertices);
		likeliest_moves();
	}
	// is it this monkey's turn?
	bool frozen(const Goku &monkey, int round_temp) {
		if (!monkey.alive) return true;
		if (monkey.kinton > 0) return false;
		if (round_temp % 2 == 1) return true;
		if (monkey.strength < moving_penalty() && (round_temp + 1) % 4 == 2) return true;
		return false;
	}
	bool frozen(int monkey_id) {
		return frozen(goku(monkey_id), round());
	}
	// update ball data + monkey paths
	void process_round() {
		update_ballz();
		for (int i = 0; i < nb_players(); i++) paths[i].update(goku(i).alive, frozen(i), goku(i).pos.i * cols() + goku(i).pos.j);
	}
	// am i chasing this one?
	bool after_monkey(int monkey_id) {
		return next.id == 0 && next.type == Ball && next.pos == goku(monkey_id).pos.i * cols() + goku(monkey_id).pos.j;
	}
	// fry everyone!
	bool worth_frying(int monkey_id) {
		/**if (goku(monkey_id).strength >= kamehame_penalty()) return true;
		int n = ball_offset + ballz.size();
		for (int i = 0; i < n; i++) if (options.eval_data[i].rival_monkeys[monkey_id].closest
				&& (options.eval_data[i].rival_monkeys[monkey_id].beats_me || graph[monkey_id][i].edge.rounds == graph[me()][i].edge.rounds) &&
				(!after_monkey(monkey_id) || (double(goku(me()).strength) / (goku(monkey_id).strength + goku(me()).strength)) < fight_tolerance)) return true;
		return false;*/
		if (!after_monkey(monkey_id) || (double(goku(me()).strength) / (goku(monkey_id).strength + goku(me()).strength)) < fight_tolerance) return true;
		return false;
	}
	// fry monkeys where appropriate
	Dir tube_away() {
		Dir d = None;
		int p1 = goku(me()).pos.i * cols() + goku(me()).pos.j;
		for (int i = 0; i < nb_players(); i++) if (i != me() && goku(i).alive) {
			int p2 = goku(i).pos.i * cols() + goku(i).pos.j;
			if (in_line(p1, p2, d) && worth_frying(i)) return d;
		}
		return None;
	}
	bool preventive_strike() {
		if (goku(me()).strength < kamehame_penalty()) return false;
		Dir d = tube_away();
		if (d == None) return false;
		throw_kamehame(d);
		return true;
	}
	// are 2 positions in line + no obstacles in between?
	bool in_line(int p1, int p2, Dir &d) {
		int r1 = p1 / cols(); int c1 = p1 % cols(); int r2 = p2 / cols(); int c2 = p2 % cols();
		if (r1 != r2 && c1 != c2) return false;
		if (r1 == r2) {
			d = Right;
			if (c1 > c2) { int t = c2; c2 = c1; c1 = t; d = Left; }
			while (c1 < c2) if (!paper[r1][c1++]) return false;
		} else {
			d = Bottom;
			if (r1 > r2) { int t = r2; r2 = r1; r1 = t; d = Top; }
			while (r1 < r2) if (!paper[r1++][c1]) return false;
		}
		return true;
	}
	// how strong is a monkey gonna be in a few moves?
	int get_strength(int moves, int monkey_id) {
		int strength = goku(monkey_id).strength;
		int mushroom = goku(monkey_id).kinton;
		for (int i = 0; i < moves; i++) {
			if (mushroom > 0) mushroom--;
			else if (strength >= moving_penalty()) strength -= moving_penalty();
			else return strength;
		}
		return strength;
	}
	// # rounds to next movement
	int next_move_in(int monkey_id) {
		int move_in = round() % 2 ? 1 : 2;
		if (has_kinton(goku(monkey_id).type)) move_in = 1;
		else if (goku(monkey_id).strength < moving_penalty()) move_in = round() % 4 ? round() % 4 : 4;
		return move_in;
	}
	// is this worth a crash?
	bool worth_fighting(int hunter_strength, int prey_strength) {
		if (hunter_strength == 0 && prey_strength == 0) return true;
		return hunter_strength / double(hunter_strength + prey_strength) >= fight_tolerance;
	}
	bool valid_monkey(int monkey_id) {
		return monkey_id != me() && goku(monkey_id).alive;  // && status(monkey_id) >= 0.0;
	}
	// tells whether you are likely to get killed here
	bool you_die_here(bool freeze, const Pos &p, int k, vector<double> &danger_factors) {
		Dir d;
		bool you_live = true;
		int move_in = next_move_in(me());
		int pos = p.i * cols() + p.j;
		int my_strength = freeze ? goku(me()).strength : get_strength(1, me());
		for (int i = 0; i < nb_players(); i++) if (i != me() && goku(i).alive) {
			int base_rival_strength = goku(i).strength;
			int rival_pos = goku(i).pos.i *cols() + goku(i).pos.j;
			// danger factor
			if (!freeze && (base_rival_strength >= kamehame_penalty() || !worth_fighting(goku(me()).strength, base_rival_strength))) {
				if (distances[rival_pos].empty()) get_distances(goku(i).pos, paper, distances[rival_pos]);
				danger_factors[k] += double(base_rival_strength) / distances[rival_pos][pos];
			}
			if (you_live) {
				// don't crash into frozen monkeys
				if (!freeze && !worth_fighting(my_strength, base_rival_strength) && pos == rival_pos) you_live = false;
				if (you_live && next_move_in(i) <= move_in) {
					// monkeys that threaten what im after deserve a kamehamedown!
					bool skip = (my_strength >= kamehame_penalty() && next.id != -1 && !(next.id == 0 && next.type == Ball) &&
							!(next.id == 0 && next.type == Capsule) && options.eval_data[next.id].rival_monkeys[i].best_bet && goku(me()).kinton < 2 &&
							graph[i][next.id].edge.rounds >= next.edge.rounds && graph[i][next.id].edge.rounds <= (next.edge.rounds + 2)) ||
							(my_strength < kamehame_penalty() && next.id >= nut_offset && next.id < mushroom_offset && cell(p).type == Bean &&
							options.eval_data[next.id].rival_monkeys[i].closing_in && graph[i][next.id].edge.rounds <= 2);
					if (!skip) {
						int rival_strength = get_strength(1, i);
						for (int j = 0; you_live && j < int(likely_moves[i].size()); j++) {
							// check for kamehames & collisions
							int rival_strength_temp = likely_moves[i][j] == rival_pos ? base_rival_strength : rival_strength;
							if ((rival_strength_temp >= kamehame_penalty() && in_line(likely_moves[i][j], pos, d)) ||
								(pos == likely_moves[i][j] && !worth_fighting(my_strength, rival_strength_temp))) you_live = false;
						}
						// scrub may lock on you before moving...
						if (you_live && base_rival_strength >= kamehame_penalty() && in_line(rival_pos, pos, d)) you_live = false;
					}
				}
			}
		}
		return !you_live;
	}
	// find out how safe positions are around me
	bool get_war_situation(vector<bool> &compromised_positions, vector<double> &danger_factors) {
		Pos p = goku(me()).pos;
		bool all_compromised = true;
		compromised_positions = vector<bool>(5); danger_factors = vector<double>(4, 0.0);
		compromised_positions[4] = you_die_here(true, p, -1, danger_factors);
		if (!compromised_positions[4]) all_compromised = false;
		for (int i = 0; i < 4; i++) {
			Pos np = dest(p, dirs[i]);
			if (paper[np.i][np.j]) {
				compromised_positions[i] = you_die_here(false, np, i, danger_factors);
				if (!compromised_positions[i]) all_compromised = false;
			}
		}
		return all_compromised;
	}
	// advance towards the provided next vertex
	bool move_to_non_compromised(const Pos & p, const vector<bool> &compromised_positions, vector<double> &danger_factors) {
		Dir d = None; double df = -1.0;
		for (int i = 0; i < 4; i++) {
			Pos np = dest(p, dirs[i]);
			if (paper[np.i][np.j] && !compromised_positions[i] && (d == None || danger_factors[i] < df) && danger_factors[i] != INF) { df = danger_factors[i]; d = dirs[i]; }
		}
		if (d != None) { move(d); return true; }
		return false;
	}
	bool move_to_closer_non_compromised(const Pos & p, const vector<bool> &compromised_positions, vector<double> &danger_factors, int distance, bool reverse) {
		Dir d = None; double df = -1.0;
		for (int i = 0; i < 4; i++) {
			Pos np = dest(p, dirs[i]);
			if (paper[np.i][np.j] && !compromised_positions[i]
					&& (reverse ? distances[next.pos][np.i * cols() + np.j] > distance : distances[next.pos][np.i * cols() + np.j] < distance)
					&& (d == None || danger_factors[i] < df) && danger_factors[i] != INF)
				{ df = danger_factors[i]; d = dirs[i]; }
		}
		if (d != None) { move(d); return true; }
		return false;
	}
	bool move_to_closer(const Pos & p, vector<double> &danger_factors, int distance, bool reverse) {
		Dir d = None; double df = -1.0;
		for (int i = 0; i < 4; i++) {
			Pos np = dest(p, dirs[i]);
			if (paper[np.i][np.j] && (reverse ? distances[next.pos][np.i * cols() + np.j] > distance : distances[next.pos][np.i * cols() + np.j] < distance)
					&& (d == None || danger_factors[i] < df) && danger_factors[i] != INF)
				{ df = danger_factors[i]; d = dirs[i]; }
		}
		if (d != None) { move(d); return true; }
		return false;
	}
	// this one goes out to all you dirty campers!
	void inflate_my_ballz(const Pos &p, int distance, vector<double> &danger_factors, bool reverse) {
		if (patience_counter++ < patience_limit) move(None);
		else { move_to_closer(p, danger_factors, distance, reverse); patience_counter = 0; }
	}
	bool one_step_at_a_time() {
		Pos p = goku(me()).pos;
		vector<bool> compromised_positions;
		vector<double> danger_factors;
		get_war_situation(compromised_positions, danger_factors);
		if (next.id == -1) {	// Hold your piss! Dodge if you have to!
			if (compromised_positions[4] && move_to_non_compromised(p, compromised_positions, danger_factors)) return true;
			move(None); return true;
		}
		// handle back-offs
		bool reverse = next.id == 0 && next.type == Capsule;
		// Did you know your monkey can spawn on top of a mushroom? Then hold still and behold the birth of a mushroom!
		int distance = distances[next.pos][p.i * cols() + p.j];
		if (!distance) { if (move_to_non_compromised(p, compromised_positions, danger_factors)) return true; }
		else if (distance == 1 && ((next.type == Bean || next.type == Kinton) && next.time > 0)) {
			if (compromised_positions[4] && move_to_non_compromised(p, compromised_positions, danger_factors)) return true;
			move(None); return true;
		}
		if (move_to_closer_non_compromised(p, compromised_positions, danger_factors, distance, reverse)) return true;
		// can't advance cos risk of crossfire and in a compromised spot, move out of the way if possible. Otherwise your ass is toast but then might as well move!
		if (compromised_positions[4]) {
			if (move_to_non_compromised(p, compromised_positions, danger_factors)) return true;
			if (move_to_closer(p, danger_factors, distance, reverse)) return true;
		} else inflate_my_ballz(p, distance, danger_factors, reverse);
		return false;
	}
	void make_a_move() { if (one_step_at_a_time()) patience_counter = 0; }
	// calculate edges between a vertex and its adjacent vertices
	void set_edges(int n, vector<bool> &b, const LVertex &vertex, vector<LVertex> &vertices) {
		for (int i = 0; i < n; i++) if (b[i]) { vertices[i].prev_id = vertex.id; vertices[i].edge = get_edge(vertex, vertices[i]); }
	}
	// erase your tracks!
	void remove_previous_vertices(vector<bool> &b, const LVertex &vertex, vector<LVertex> &vertices) {
		b[vertex.id] = false;
		int prev = vertex.prev_id;
		while (prev != -1) {
			b[prev] = false;
			prev = vertices[prev].prev_id;
		}
	}
	// is a vertex risk-free?
	bool safe_to_win(const LVertexEval &vertex_eval) {
		if (!vertex_eval.win_it) for (int i = 0; i < nb_players(); i++)
			if (i != me() && goku(i).alive && vertex_eval.rival_monkeys[i].beats_me && !vertex_eval.rival_monkeys[i].wimp) return false;
		return true;
	}
	// try going from each vertex to the others: no need for this so far as more immediate data analysis provides consistent results
	// basis for a recursive analysis, ie. backtracking
	LOptions next_steps(int n, vector<LVertex> &vertices) {
		LOptionData bod; bod.root.id = -1;
		LOptions o(n, bod);
		for (int i = 0; i < n; i++) {
			vector<bool> b(n, true);
			vector<LVertex> vertices_temp = vertices;
			LVertex vertex = vertices_temp[i];
			remove_previous_vertices(b, vertex, vertices_temp);
			set_edges(n, b, vertex, vertices_temp);
			o[i] = get_option_data(n, b, vertex, vertices_temp);
		}
		return o;
	}
	// need this stuff for next pick up?
	bool gonna_need_mushroom(bool ballsy, const LVertex &vertex, const set<LVertex> &pod_set, const set<LVertex> &ball_set) {
		if (options.eval_data[vertex.id].win_it && goku(me()).kinton < kinton_life_time()) return true;
		if (options.eval_data[vertex.id].nick_it) for (int i = 0; i < nb_players(); i++)
			if (i != me() && goku(i).alive && options.eval_data[vertex.id].rival_monkeys[i].best_bet && is_wimpy(goku(i).strength) &&
					options.eval_data[vertex.id].time_frame < NICK_RADIUS && vertex.time < NICK_RADIUS) return true;
		if (ballsy) return is_slow(pod_set.begin()->edge.mushroom);
		return ball_set.empty() ? true : is_slow(ball_set.begin()->edge.mushroom);
	}
	bool gonna_need_nut(bool ballsy, const LVertex &vertex, const set<LVertex> &pod_set, const set<LVertex> &ball_set) {
		if (options.eval_data[vertex.id].win_it && options.eval_data[vertex.id].edge_eval.mushroom > 0 && goku(me()).strength < max_strength()) return true;
		if (options.eval_data[vertex.id].nick_it) for (int i = 0; i < nb_players(); i++)
			if (i != me() && goku(i).alive && options.eval_data[vertex.id].rival_monkeys[i].best_bet && is_wimpy(goku(i).strength) &&
					options.eval_data[vertex.id].time_frame < NICK_RADIUS && vertex.time < NICK_RADIUS) return true;
		if (goku(me()).strength >= strength_upper_bound) return false;
		if (ballsy) return is_wimpy(pod_set.begin()->edge.strength);
		return ball_set.empty() ? true : is_wimpy(ball_set.begin()->edge.strength);
	}
	// extra multiplier for vertices with interesting stuff nearby
	double look_into_the_future(bool ballsy, double vertex_multiplier, const LVertex &vertex) {
		// if a strong monkey is wandering around the place, the vertex gets bad multiplier
		for (int i = 0; i < nb_players(); i++)
			if (i != me() && goku(i).alive && options.eval_data[vertex.id].rival_monkeys[i].beats_me && !options.eval_data[vertex.id].rival_monkeys[i].wimp)
				return vertex_multiplier * threat_mult;
		// if it isn't compromised, search for nearby pods or balls
		bool find_pods = (ballsy && (vertex.type == Bean || vertex.type == Kinton)) || (!ballsy && vertex.type == Ball);
		int offset = find_pods ? pod_offset : ball_offset;
		int m = find_pods ? nb_capsules() : ballz.size();
		int n = ball_offset + ballz.size();
		vector<bool> b(n, false);
		for (int i = 0; i < m; i++) b[offset + i] = true;
		LVertex vertex_temp = vertex;
		vector<LVertex> vertices_temp = graph[me()];
		remove_previous_vertices(b, vertex, vertices_temp);
		apply_type(vertex_temp);
		set_edges(n, b, vertex_temp, vertices_temp);
		LOptionData op_data = get_option_data(n, b, vertex_temp, vertices_temp);
		set<LVertex> vertex_set = find_pods ? get_pod_set(vertices_temp) : get_ball_set(vertices_temp);
		bool loop = true;
		for (set<LVertex>::iterator it = vertex_set.begin(); loop && it != vertex_set.end(); it++) if (safe_to_win(op_data.eval_data[it->id]))
			{ vertex_multiplier += bonus_mult / (op_data.eval_data[it->id].edge_eval.rounds - vertex_temp.edge.rounds); loop = false; }
		return vertex_multiplier;
	}
	// each vertex type yields their own multiplier
	double get_vertex_multiplier(bool ballsy, LVertexRating &vertex_rating, const LVertex &vertex, const vector<LVertexEval> &eval, const set<LVertex> &pod_set, const set<LVertex> &ball_set) {
		double vertex_multiplier = default_mult;
		if (vertex.type == Ball) vertex_multiplier = ballsy ? ball_mult : look_into_the_future(ballsy, non_ball_mult, vertex);
		else if (vertex.type == Capsule) vertex_multiplier = ballsy ? look_into_the_future(ballsy, pod_mult, vertex) : non_pod_mult;
		else if (vertex.type == Bean) vertex_multiplier = gonna_need_nut(ballsy, vertex, pod_set, ball_set) ?
				look_into_the_future(ballsy, nut_mult, vertex) : non_nut_mult;
		else if (vertex.type == Kinton) vertex_multiplier = gonna_need_mushroom(ballsy, vertex, pod_set, ball_set) ?
				look_into_the_future(ballsy, mushroom_mult, vertex) : non_mushroom_mult;
		return vertex_multiplier;
	}
	// come up with a rating for a vertex in the provided context
	void rate_vertex(bool ballsy, LVertexRating &vertex_rating, const LVertex &vertex, const vector<LVertexEval> &eval, const set<LVertex> &pod_set, const set<LVertex> &ball_set) {
		if (vertex.edge.rounds) {
			double win_multiplier = eval[vertex.id].win_it ? win_mult : non_win_mult;
			double vertex_multiplier = get_vertex_multiplier(ballsy, vertex_rating, vertex, eval, pod_set, ball_set);
			vertex_rating.win_it = eval[vertex.id].win_it;
			vertex_rating.rating = vertex_multiplier * win_multiplier / vertex.edge.rounds;
		} else vertex_rating.rating = null_rating;
		vertex_rating.vertex = vertex;
	}
	// calculates the cost of chasing down a monkey
	int rounds_to_touchdown(Goku &my_monkey, Goku &rival_monkey) {
		int d1 = 0;
		int d2 = distances[rival_monkey.pos.i * cols() + rival_monkey.pos.j][my_monkey.pos.i * cols() + my_monkey.pos.j];
		int round_temp = round();
		while (d1 < d2) {
			if (my_monkey.strength < moving_penalty() && rival_monkey.strength < moving_penalty()) return -1;
			if (!frozen(my_monkey, round_temp)) {
				if (my_monkey.kinton > 0) my_monkey.kinton--;
				else if (my_monkey.strength >= moving_penalty()) my_monkey.strength -= moving_penalty();
				d1++;
			}
			if (!frozen(rival_monkey, round_temp)) {
				if (rival_monkey.kinton > 0) rival_monkey.kinton--;
				else if (rival_monkey.strength >= moving_penalty()) rival_monkey.strength -= moving_penalty();
				d2++;
			}
			round_temp++;
		}
		return round_temp - round();
	}
	// mind other monkeys hunting the same prey
	void apply_hunter_tax(int i, int rounds_count, LVertexRating &rival_rating) {
		for (int j = 0; j < nb_players(); j++) if (j != me() && j != i && goku(j).alive && !is_wimpy(goku(j).strength)) {
			int p1 = goku(j).pos.i * cols() + goku(j).pos.j;
			if (distances[p1].empty()) get_distances(goku(j).pos, paper, distances[p1]);
			Goku hunter = goku(j);
			Goku prey = goku(i);
			int hunter_rounds_count = rounds_to_touchdown(hunter, prey);
			if (hunter_rounds_count > 0 && !is_wimpy(hunter.strength) && hunter_rounds_count < rounds_count) { rival_rating.rating *= threat_mult; return; }
		}
	}
	// find wimpy monkeys to prey upon
	void add_monkey_vertices(vector<LVertexRating> &ratings) {
		for (int i = 0; i < nb_players(); i++) if (i != me() && goku(i).alive && goku(i).strength < real_strength_lower_bound) {
			Goku my_monkey = goku(me());
			Goku rival_monkey = goku(i);
			int p = goku(i).pos.i * cols() + goku(i).pos.j;
			if (distances[p].empty()) get_distances(goku(i).pos, paper, distances[p]);
			int rounds_count = rounds_to_touchdown(my_monkey, rival_monkey);
			if (rounds_count > 0 && !is_wimpy(my_monkey.strength)) {
				bool win_em_all = true;
				int m = nb_beans() + nb_kintons();
				for (int j = 0; win_em_all && j < m; j++) if (graph[i][j].edge.rounds < rounds_count) win_em_all = false;
				if (win_em_all) {
					double rival_multiplier = cannon_fodder_mult / rounds_count;
					LVertexRating rival_rating;
					rival_rating.win_it = true; rival_rating.rating = rival_multiplier; rival_rating.vertex.id = 0;
					rival_rating.vertex.type = Ball; rival_rating.vertex.pos = p;
					apply_hunter_tax(i, rounds_count, rival_rating);
					ratings.push_back(rival_rating);
				}
			}
		}
	}
	bool stalking_my_ass(int monkey_id) {
		if (paths[monkey_id].steps.size() < STEPS_SIZE) return false;
		int pos = goku(me()).pos.i * cols() + goku(me()).pos.j;
		if (distances[pos].empty()) get_distances(goku(me()).pos, paper, distances[pos]);
		int last = MAX_INT;
		for (list<int>::iterator it = paths[monkey_id].steps.begin(); it != paths[monkey_id].steps.end(); it++) {
			if (distances[pos][*it] > last) return false;
			last = distances[pos][*it];
		}
		return true;
	}
	// are they stalking my weakling ass?
	void add_prey_vertex(vector<LVertexRating> &ratings) {
		if (is_wimpy(goku(me()).strength)) { // if (goku(me()).strength <= real_strength_lower_bound)
			for (int i = 0; i < nb_players(); i++) if (i != me() && goku(i).alive &&
					(!is_wimpy(goku(i).strength) || worth_fighting(goku(i).strength, goku(me()).strength)) && stalking_my_ass(i)) {
				int pos = goku(me()).pos.i * cols() + goku(me()).pos.j;
				int rival_pos = goku(i).pos.i * cols() + goku(i).pos.j;
				int dist = distances[pos][rival_pos];
				int strength = goku(i).strength;
				int mushroom = goku(i).kinton;
				int rounds_count = get_costly(dist, strength, mushroom);
				if (rounds_count < proximity_limit) {
					bool win_em_all = true;
					int m = nb_beans() + nb_kintons();
					for (int j = 0; win_em_all && j < m; j++) if (graph[me()][j].edge.rounds < rounds_count) win_em_all = false;
					if (win_em_all) {
						// what, muthafucka tryinna play me! git yo sawy ass outta there!!!
						if (distances[rival_pos].empty()) get_distances(goku(i).pos, paper, distances[rival_pos]);
						double rival_multiplier = MAX_DOUBLE / rounds_count;
						LVertexRating prey_rating;
						prey_rating.win_it = true; prey_rating.rating = rival_multiplier; prey_rating.vertex.id = 0;
						prey_rating.vertex.type = Capsule; prey_rating.vertex.pos = rival_pos;
						ratings.push_back(prey_rating);
					}
				}
			}
		}
	}
	// bite the bullet!
	void what_would_brian_boitano_do() {
		bool ballsy = has_ball(goku(me()).type);
		set<LVertex> pod_set = get_pod_set(graph[me()]);
		set<LVertex> ball_set = get_ball_set(graph[me()]);
		int n = ball_offset + ballz.size();
		vector<LVertexRating> vertex_ratings(n);
		for (int i = 0; i < n ; i++) rate_vertex(ballsy, vertex_ratings[i], graph[me()][i], options.eval_data, pod_set, ball_set);
		add_monkey_vertices(vertex_ratings);
		add_prey_vertex(vertex_ratings);
		sort(vertex_ratings.begin(), vertex_ratings.end());
		next = vertex_ratings[0].vertex;
	}
	// Find vertices that provide points within the time limit
	bool last_call(const set<LVertex> &vertex_set, const vector<LVertex> &vertices, const LOptionData &op_data) {
		for (set<LVertex>::iterator it = vertex_set.begin(); it != vertex_set.end(); it++)
			if (safe_to_win(op_data.eval_data[it->id]) && vertices[it->id].edge.rounds + round() < nb_rounds()) {
				LVertex vertex = *it; while (vertex.prev_id != -1) vertex = vertices[vertex.prev_id];
				next = vertex; return true;
			}
		return false;
	}
	// Pot those last balls, otherwise find one last bean to maximize score
	void cheapskate_mode() {
		int n = ball_offset + ballz.size();
		vector<bool> b(n, true);
		vector<bool> bn = b;
		vector<LVertex> vertices = graph[me()];
		LVertex monkey = get_monkey_vertex(me());
		shortest_path(n, bn, vertices);
		LOptionData op_data = get_option_data(n, b, monkey, vertices);
		if (has_ball(goku(me()).type)) {
			if (last_call(get_pod_set(vertices), vertices, op_data)) return;
			if (last_call(get_nut_set(vertices), vertices, op_data)) return;
		} else {
			set<LVertex> ball_set = get_ball_set(vertices);
			for (set<LVertex>::iterator it = ball_set.begin(); it != ball_set.end(); it++)
				if (safe_to_win(op_data.eval_data[it->id]) && vertices[it->id].edge.rounds + round() < nb_rounds()) {
					bn = b;
					vector<LVertex> ball_vertices = vertices;
					remove_previous_vertices(bn, *it, ball_vertices);
					set_edges(n, bn, *it, ball_vertices);
					shortest_path(n, bn, ball_vertices);
					LOptionData ball_op_data = get_option_data(n, b, monkey, ball_vertices);
					if (last_call(get_pod_set(ball_vertices), ball_vertices, ball_op_data)) return;
				}
			if (last_call(get_nut_set(vertices), vertices, op_data)) return;
		}
		next.id = -1;  // save your breath!
	}
	// determine whether a monkey is wimpy or slow
	bool is_wimpy(int strength) const { return strength < strength_lower_bound; }
	bool is_slow(int mushroom) const { return mushroom < mushroom_lower_bound; }
	// prepare everything for round
	void prepare_all() {
		random_shuffle(dirs, dirs + 4);  // randomness in move decision
		prepare_vertices();
		prepare_tracks();
		prepare_traversal();
	}
	// do as the method name says
	bool first_things_first_and_return() {
		if (!round()) init_all();
		process_round();
		return frozen(me());
	}
	// this is where the actual decision making gets done!
	void get_ready_to_rumble() {
		prepare_all();
		if (round() >= cheapskate_time) cheapskate_mode();
		else what_would_brian_boitano_do();
		if (!preventive_strike()) make_a_move();
	}
	// Runs every round!
	virtual void play () {
		if (first_things_first_and_return()) return;
		get_ready_to_rumble();
	}

};
RegisterPlayer(PLAYER_NAME);