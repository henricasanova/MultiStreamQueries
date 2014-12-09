//#ifndef OPTIMALDNF_HPP
//#define OPTIMALDNF_HPP

#include <cmath>

#include <math.h>
#include <time.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <stack>
#include <cfloat>
#include <set>
#include <map>
#include <boost/lexical_cast.hpp>

#include <boost/assign/list_of.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>


#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include <boost/math/distributions/uniform.hpp>
#include <boost/random.hpp>
#include <boost/random/mersenne_twister.hpp>

#include <stdio.h>
#include <stdlib.h>

using namespace std;
#define MYDEBUG 0
#define DEBUG 0
#define DEBUG1 0
#define DEBUG2 0
#define DEBUGBORDER 1
#define Greedy 1
#define ProgDyn 0
#define Heuristiques 0
#define OPTIMAL 1
#define PRINTSTATS 0
#define INDEBUG 0
#define WITHPROGRESS 0
#define TIMING
#define LEGACY_MODE 0
#define DEBUGMULTIGREEDY 0

typedef struct{
	//int nb_streams;
    //int * stream;
    int * nb_data_recup;
    long double proba;
    int full_eval;
    int eval_order;
} leaf;

typedef struct{
    bool vu;
    long double cost;
    int next_stream;
    std::vector<int> vector_value;
} case_elem;

typedef struct{
	bool used;
	int stream_id;
	int n_elements;
	int and_id;
	int leaf_id;
	long double gain;
} stream_lipyeow;

typedef struct{
	int stream_id;
	int n_elements;
	int and_id;
	int leaf_id;
} leaf4lipyeow;

typedef boost::tuples::tuple<long double, int> ratio_and;
typedef boost::tuples::tuple<long double, int, int> ratio_leaf;
typedef boost::tuples::tuple<int, int> leaf_place;
//Feuille contient nb_recup, stream, proba, and, place
typedef boost::tuples::tuple<int, int, long double, int, int> Feuille;
typedef boost::tuples::tuple<long double, int> Andratio;

typedef boost::tuples::tuple< int, int, int, long double> FeuilleIncrement;


unsigned long int convertvectorto_code( std::vector<int> vector_max, std::vector<int> vector, int nb_stream );
long double prog_dyn_DNF(unsigned long int cas, leaf ** DNF, int nb_stream, long double * streamCost, int nb_and , int * nb_leafs_and,
                         std::vector< case_elem > & marqueurs, std::vector<int> & vector_max, int nb_cases, std::vector<int> & best_stream_order);

//long double glouton( int nb_stream, long double *  streamCost, int & Sum_max_recup, std::vector< multiset <Feuille> > & disjoint_set,long double & best_glouton, long double proba_prec,std::vector< int > & solution);
//long double glouton(int nb_stream, long double * streamCost,int & Sum_max_recup, std::vector<  multiset<Feuille> > & disjoint_set,
// long double & best_glouton, long double proba_prec,
//std::vector<int> & solution);

long double glouton_stream(leaf ** DNFTree,int nb_and, int * nb_leafs_and, int NumAND,std::vector<int> & AndFulleval, int nb_stream, long double * streamCost, int & Sum_max_recup,
                           std::vector<multiset<Feuille> > & disjoint_set, long double & best_glouton,
                           long double proba_prec, std::vector<int> & solution);

void
newglouton(leaf ** DNFTree, int nb_stream, int nb_and, int * nb_leafs_and, long double * streamCost, int & leaf_rest, long double & cost_min,
           std::vector<multiset<Feuille> > & disjoint_set, vector< leaf_place> & final_order);



void eval_andbyand_byratio(leaf ** DNF, int nb_and, int * nb_leafs_and, long double * streamCost, vector<long double> proba_and, int nb_stream,
                           long double & meilleurcost, multiset<int> & and_rest, std::vector<multiset<Feuille> > & disjoint_set, vector<leaf_place> & evaluation_order, long double heur);

void eval_andbyand_bycsurp(leaf ** DNF, int nb_and, int * nb_leafs_and, long double * streamCost,  vector< long double> proba_and, int nb_stream,
                           long double & meilleurcost, multiset<int> & and_rest,
                           std::vector<multiset<Feuille> > & disjoint_set, vector< leaf_place> & evaluation_order);
void eval_andbyand_bycost(leaf ** DNF, int nb_and, int * nb_leafs_and, long double * streamCost,  vector< long double> proba_and, int nb_stream,
                          long double & meilleurcost, multiset<int> & and_rest,
                          std::vector<multiset<Feuille> > & disjoint_set, vector< leaf_place> & evaluation_order);
void eval_andbyand_bydecreasingproba(leaf ** DNF, int nb_and, int * nb_leafs_and, long double * streamCost, vector<long double> proba_and, int nb_stream,
                                     long double & meilleurcost, multiset<int> & and_rest, std::vector<multiset<Feuille> > & disjoint_set, vector<leaf_place> & evaluation_order);



long double orderleaves_byratio(leaf ** DNF, int nb_and, int * nb_leafs_and,
		int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order, long double heur);

long double orderleaves_bycsurq(leaf ** DNF, int nb_and, int * nb_leafs_and, int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order);

long double orderleaves_bycsurp(leaf ** DNF, int nb_and, int * nb_leafs_and, int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order);

long double orderleaves_bycost(leaf ** DNF, int nb_and, int * nb_leafs_and,  int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order);

long double orderleaves_bydecreasingproba(leaf ** DNF, int nb_and, int * nb_leafs_and, int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order);

long double orderleaves_byincreasingproba(leaf ** DNF, int nb_and, int * nb_leafs_and, int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order);



void order_andby_csurp(leaf ** DNF, int nb_and, int * nb_leafs_and, long double * streamCost,  vector< long double> proba_and, int nb_stream,
                       long double & meilleurcost, multiset<int> and_rest, multiset<ratio_and> and_final_order, vector< vector< leaf_place> > leaf_order,
                       std::vector<multiset<Feuille> > & disjoint_set, vector< leaf_place> evaluation_order);

void order_andby_cost(leaf ** DNF, int nb_and, int * nb_leafs_and, long double * streamCost,  vector< long double> proba_and, int nb_stream,
                      long double & meilleurcost, multiset<int> and_rest, multiset<ratio_and> and_final_order, vector< vector< leaf_place> > leaf_order,
                      std::vector<multiset<Feuille> > & disjoint_set, vector< leaf_place> evaluation_order);

void order_andby_increasingproba(leaf ** DNF, int nb_and, int * nb_leafs_and,
                                 long double * streamCost, vector<long double> proba_and, int nb_stream,
                                 long double & meilleurcost, multiset<int> and_rest, multiset<ratio_and> and_final_order, vector<vector<leaf_place> > leaf_order,
                                 std::vector<multiset<Feuille> > & disjoint_set, vector<leaf_place> evaluation_order);

void order_andby_decreasingproba(leaf ** DNF, int nb_and, int * nb_leafs_and,
                                 long double * streamCost, vector<long double> proba_and, int nb_stream,
                                 long double & meilleurcost, multiset<int> and_rest, multiset<ratio_and> and_final_order,
                                 vector<vector<leaf_place> > leaf_order, std::vector<multiset<Feuille> > & disjoint_set, vector<leaf_place> evaluation_order);




long double
Cost(leaf ** DNFTree, int nb_and, int * nb_leafs_and, int nb_stream, long double * streamCost, vector< leaf_place> evaluation_order);

long double
Cost4Arrays(leaf ** DNFTree, int nb_and, int * nb_leafs_and, int nb_stream, long double * streamCost, int nb_leaves, int * and_id, int * leaf_id);

long double
Cost4Arrays_optimized(leaf ** DNFTree, int nb_and, int * nb_leafs_and, int nb_stream, long double * streamCost, int nb_leaves, int * and_id, int * leaf_id);

long double
Cost4Arrays_stripped(leaf ** DNFTree, int nb_and, int * nb_leafs_and, long double * streamCost,
		int nb_leaves, int rank_first_leaf, int rank_last_leaf, int * and_id, int * leaf_id, int nb_streams, int * max_elements_per_stream,
		bool *** AND_needs_data, long double *** proba_data_read, long double * probaAndTrue, bool * andCompleted);

void
exhaustive_andbyand(leaf ** DNFTree, int nb_and, int * nb_leavesperAND,
                      long double * streamCost, vector<long double> proba_and, int nb_stream,
                      long double & meilleurcost);

void
exhaustive_andbyand_singlestream(leaf ** DNFTree, int nb_and, int * nb_leavesperAND,
                      long double * streamCost, vector<long double> proba_and, int nb_streams,
                      long double & optimal_cost);

void
exhaustive_andbyand_original(leaf ** DNFTree, int nb_and, int * nb_leavesperAND,
                      long double * streamCost, vector<long double> proba_and, int nb_stream,
                      long double & meilleurcost);

void sillykernel(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
		long double * streamCost, int and_id, long double & bestcost,
		vector<leaf_place> & final_order);

void MultiStreamGreedy(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
		long double * streamCost, int and_id, long double & bestcost,
		vector<leaf_place> & final_order);


