/* Copyright (c) 2013 Dounia Zaidouni and Frédéric Vivien. All rights reserved.            */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <iostream>
#include "DNFScheduling.hpp"
#include <set>
#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <fstream>

using namespace std;

//
// Transformation of any leaf order (stored in a vector) into a and-by-and leaf order (stored in arrays)
//
void evaluation_order_conversion(int nb_ands, int * nb_leaves_per_and, vector<leaf_place> & original_order, int * new_order_and_id, int * new_order_leaf_id){
	// Data structure to record how many leaves of an AND have been scheduled so far
	int * n_leaves_scheduled = new int [nb_ands];
	for(int and_id=0; and_id<nb_ands; and_id++){
		n_leaves_scheduled[and_id] = 0;
	}
	// Data structure to record the order in which ANDs complete
	int * and_id_from_rank = new int [nb_ands];
	int n_ands_completed = 0;
	// Temporary data structure to record the leaf ordering for each AND
	int ** ordered_leaves_for_and = new int * [nb_ands];
	int * nb_leaves_stored = new int [nb_ands];
	for(int and_id=0; and_id<nb_ands; and_id++){
		ordered_leaves_for_and[and_id] = new int [nb_leaves_per_and[and_id]];
		nb_leaves_stored[and_id] = 0;
	}
	// Computation of AND completion order
    for (vector<leaf_place>::iterator leaf_it = original_order.begin(); leaf_it < original_order.end(); leaf_it++){
    	int this_leaf_id  = leaf_it->get<1> ();
    	int this_leaf_and = leaf_it->get<0> ();
    	n_leaves_scheduled[this_leaf_and]++;
    	// Store this leaf in the data structure associated to its AND
    	ordered_leaves_for_and[this_leaf_and][nb_leaves_stored[this_leaf_and]] = this_leaf_id;
    	nb_leaves_stored[this_leaf_and]++;
    	// Check whether we just completed that AND
    	if(n_leaves_scheduled[this_leaf_and]==nb_leaves_per_and[this_leaf_and]){
    		and_id_from_rank[n_ands_completed] = this_leaf_and;
    		n_ands_completed++;
    	}
    }
    // We check that all the ANDs have been fully processed
    assert(n_ands_completed==nb_ands);
    // We copy the new order in the output arrays
    int total_leaves_stored = 0;
    for(int and_rank=0; and_rank<nb_ands; and_rank++){
    	int and_id = and_id_from_rank[and_rank];
    	for(int leaf_rank=0; leaf_rank<nb_leaves_per_and[and_id]; leaf_rank++){
    		new_order_and_id[total_leaves_stored] = and_id;
    		new_order_leaf_id[total_leaves_stored] = ordered_leaves_for_and[and_id][leaf_rank];
    		total_leaves_stored++;
    	}
    }

    delete [] n_leaves_scheduled;
    delete [] and_id_from_rank;
	for(int and_id=0; and_id<nb_ands; and_id++){
		delete [] ordered_leaves_for_and[and_id];
	}
	delete [] ordered_leaves_for_and;
	delete [] nb_leaves_stored;
}

//
// Helper function for the dynamic programming algorithm
// Transform a configuration coded as a vector into an int
//
unsigned long int
convertvectorto_code(std::vector<int> vector_max, std::vector<int> vector, int nb_streams)
{

    unsigned long int code = 0;
    int * Max = new int[nb_streams];
    for (int i = 0; i < nb_streams; i++)
    {
        Max[i] = 1;
    }

    for (int i = 0; i < nb_streams - 1; i++)
    {
        for (int d = i; d < nb_streams - 1; d++)
        {
            Max[i] *= (vector_max[d + 1] + 1);
        }
    }


    for (int s = 0; s < nb_streams - 1; s++)
    {

        code += (vector[s] * Max[s]);
    }

    code += vector[nb_streams - 1];

    delete [] Max;

    return code;
}

//
// The dynamic program to compute the optimal data retrieval order
// (which is not the optimal leaf ordering)
//
long double
prog_dyn_DNF(unsigned long int cas, leaf ** DNF, int nb_streams,
             long double * streamCost, int nb_ands, int * nb_leaves_per_and,
             std::vector<case_elem> & marqueurs, std::vector<int> & vector_max,
             unsigned long int nb_cases, std::vector<int> & best_stream_order)
{
	std::vector<int> vector_global(nb_streams, 0);

	long double BestCost;
	unsigned long int code;
	int next_stream = 0;
	unsigned long int code_suiv;
	long double prog_dyn;
	long double bestprog_dyn;

	if (marqueurs[cas].vector_value == vector_max){
		return 0;
	}
	else{
		// If the value has never been computed, we compute and store it
		if (marqueurs[cas].vu == false){
			// Declaration and allocation of all the data structures needed
			bool * andCompleted = new bool[nb_ands];
			long double * probaAndTrue = new long double[nb_ands];

			bool ** andNeedStream = new bool *[nb_ands];
			bool ** leafCompleted = new bool *[nb_ands];

			//Check whether AND-clause was already fully evaluated
			for (int j = 0; j < nb_ands; j++){
				//Initialization of all the data structures needed
				andCompleted[j] = true;
				probaAndTrue[j] = 1;
				andNeedStream[j] = new bool[nb_streams];
				for (int s = 0; s < nb_streams; s++)
				{
					andNeedStream[j][s] = false;
				}

				leafCompleted[j] = new bool[nb_leaves_per_and[j]];
				for (int i = 0; i < nb_leaves_per_and[j]; i++){
					leafCompleted[j][i] = true;
					for (int s = 0; s < nb_streams; s++){
						// If there were so far fewer elements retrieved from the stream the leaf depends upon than what the leaf needs
						// then neither the leaf not its AND are completed, and the AND needs data from that stream
						if ((DNF[j][i].stream == s)
								&& (marqueurs[cas].vector_value[s]
								                                < DNF[j][i].nb_data_recup))
						{
							andCompleted[j] = false;
							leafCompleted[j][i] = false;
							andNeedStream[j][s] = true;
						}
					}

					if (leafCompleted[j][i] == true){
						probaAndTrue[j] = probaAndTrue[j] * DNF[j][i].proba;
					}
				}
			}
			for (int j = 0; j < nb_ands; j++){
				delete [] leafCompleted[j];
			}
			delete [] leafCompleted;

			long double probaAllCompletedAndsFalse = 1;

			for (int j = 0; j < nb_ands; j++){
				if (andCompleted[j] == true){
					probaAllCompletedAndsFalse = probaAllCompletedAndsFalse * (1 - probaAndTrue[j]);
				}
			}

			BestCost = DBL_MAX;
			marqueurs[cas].next_stream = -1;

			long double * probaStreamRead = new long double[nb_streams];
			long double * Cost = new long double[nb_streams];

			for (int s = 0; s < nb_streams; s++){
				if (marqueurs[cas].vector_value[s] < vector_max[s]){
					long double probaAllNeedingAndsFalse = 1;

					for (int j = 0; j < nb_ands; j++){
						if ((andCompleted[j] == false) && (andNeedStream[j][s] == true)){
							probaAllNeedingAndsFalse = probaAllNeedingAndsFalse * (1 - probaAndTrue[j]);
						}
					}

					probaStreamRead[s] = probaAllCompletedAndsFalse * (1 - probaAllNeedingAndsFalse);

					std::vector<int> vector(nb_streams, 0);
					vector = marqueurs[cas].vector_value;
					vector[s] = marqueurs[cas].vector_value[s] + 1;
					code = convertvectorto_code(vector_max, vector, nb_streams);
					marqueurs[code].vector_value = vector;

					prog_dyn = prog_dyn_DNF(code, DNF, nb_streams, streamCost,
							nb_ands, nb_leaves_per_and, marqueurs, vector_max, nb_cases,
							best_stream_order);
					Cost[s] = probaStreamRead[s] * streamCost[s] + prog_dyn;

					if (Cost[s] < BestCost)
					{
						BestCost = Cost[s];
						next_stream = s;
						code_suiv = code;
						bestprog_dyn = prog_dyn;

					}

					marqueurs[cas].vu = true;
					marqueurs[cas].cost = BestCost;
					marqueurs[cas].next_stream = next_stream;

				}
			}
			if (DEBUG)
			{
				cout << "probaStreamRead[" << next_stream << "]:"
						<< probaStreamRead[next_stream] << " ,bestprog_dyn :"
						<< bestprog_dyn << " ,cas_suiv :" << code_suiv << endl;
				cout << "cas :" << cas << " ,next_stream :" << next_stream
						<< " ,BestCost :" << BestCost << endl;

			}
			delete [] probaStreamRead;
			delete [] Cost;
			// Storing the solution
			if ((marqueurs[cas].vector_value == vector_global) && (marqueurs[cas].vu == true))
			{

				std::vector<int> vector_temp(nb_streams, 0);
				int i;
				unsigned long int code_t = 0;

				while (code_t < (nb_cases - 1))
				{
					i = 0;
					while (i < nb_streams)
					{
						if (marqueurs[code_t].next_stream == i)
						{

							best_stream_order.push_back(i);
							vector_temp = marqueurs[code_t].vector_value;
							vector_temp[i] = vector_temp[i] + 1;
							code_t = convertvectorto_code(vector_max, vector_temp, nb_streams);
						}
						i++;
					}
				}
			}

			for (int j = 0; j < nb_ands; j++){
				delete [] andNeedStream[j];
			}
			delete [] andNeedStream;
			delete [] probaAndTrue;
			delete [] andCompleted;
		}
	}
	return marqueurs[cas].cost;
}

//
// Build and evaluate a and-by-and leaf order based on a data retrieval order
// (typically built by the dynamic program)
//
long double
Costprog_dyn_DNF(leaf ** DNF, int nb_streams, long double * streamCost,
                 int nb_ands, int * nb_leaves_per_and, std::vector<int> compteur,
                 std::vector<int> best_stream_order, vector<leaf_place> & evaluation_order)
{

	multiset<ratio_leaf> leaves_order;

	// Build a leaf order from a data retrieval order
	// Traversal of the data retrieval order
	for (std::vector<int>::iterator it = best_stream_order.begin(); it < best_stream_order.end(); it++){
		compteur[(*it)]++;
		// Loop on all the leaves
		for (int j = 0; j < nb_ands; j++){
			for (int i = 0; i < nb_leaves_per_and[j]; i++){
				// If the data requirements of that leaf are exactly satisfied by the last data retrieved
				// the leaf is added next on the evaluation order
				if ((DNF[j][i].stream == (*it)) && (DNF[j][i].nb_data_recup == compteur[(*it)])){
					long double proba = DNF[j][i].proba;
					leaves_order.insert(ratio_leaf(proba, j, i));
				}
			}
		}
		for (multiset<ratio_leaf>::iterator it1 = leaves_order.begin(); it1 != leaves_order.end(); it1++){
			evaluation_order.push_back(leaf_place(it1->get<1> (), it1->get<2> ()));
		}
		leaves_order.clear();
	}
	if(DEBUG2){
		for (vector<leaf_place>::iterator it2 = evaluation_order.begin(); it2 < evaluation_order.end(); it2++){
			cout << " and :" << it2->get<0> () << " leaf_place :" << it2->get<1> () << endl;
		}
	}

	//
	// Transforming any leaf order into a AND-by-AND leaf order
	//
	// Computation of the total number of leaves
	int nb_leaves = 0;
	for(int and_id=0; and_id<nb_ands; and_id++){
		nb_leaves += nb_leaves_per_and[and_id];
	}
	// Allocation of the needed data structure
	int * order_and_id = new int [nb_leaves];
	int * order_leaf_id = new int [nb_leaves];
	// Order transformation
	evaluation_order_conversion(nb_ands, nb_leaves_per_and, evaluation_order, order_and_id, order_leaf_id);
	// Order evaluation
	long double optimized_cost = Cost4Arrays(DNF, nb_ands, nb_leaves_per_and, streamCost,
			nb_leaves, order_and_id, order_leaf_id);
	if(DEBUG2){
		cout << "################## Best cost ############################# "
				<< optimized_cost << endl;
	}
	return (optimized_cost);
}


//
// Generic driver for the and-by-and DYNAMIC heuristics
//
void
eval_andbyand_dynamic_ratio(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                      long double * streamCost, vector<long double> proba_and, int nb_streams,
                      long double & bestcost,
                      multiset<int> & and_rest,
                      vector<leaf_place> & evaluation_order,
                      long double heur)
{
	// Ordered data structure to store the objective values of the different ANDs
	multiset<ratio_and> and_final_order;
	// Data structure to store the leaf order for each AND
	vector<leaf_place> initleaf_place;
	vector<vector<leaf_place> > leaf_order(nb_ands, (initleaf_place));

    vector<leaf_place> optimal_leaf_order;
    long double cost;
    long double prec_bestcost = bestcost;
    multiset<int>::iterator it;
    int bestand = 0;
    long double ratio = 1;
    long double min = DBL_MAX;
    
    
    if(DEBUG2){
        multiset<int>::iterator it0;
        for (it0 = and_rest.begin(); it0 != and_rest.end(); it0++)
        {
            
            cout << *it0 << " , ";
        }
        cout << endl;
    }
    
    // While there remain some unsechduled ANDs
    if (!and_rest.empty())
    {
    	// Loop on all the unscheduled ANDs
        for (it = and_rest.begin(); it != and_rest.end(); it++)
        {
            if (DEBUG1)
            {
                cout << "Starting the processing of AND: " << *it << endl;
            }
        	// Data structure to hold, for each stream, the multiset of leaves using data from that stream
            multiset<Feuille> myset_feuille;
            std::vector<multiset<Feuille> > disjoint_set(nb_streams, (myset_feuille));
            // We copy the order built so far
            vector<leaf_place> final_order = evaluation_order;
            // We build for each stream the subset of the leaves that use data from it
            for (int i = 0; i < nb_leaves_per_and[*it]; i++)
            {
                for (int s = 0; s < nb_streams; s++)
                {
                    if (DNF[*it][i].stream == s)
                    {
                        (disjoint_set[s]).insert(boost::tuples::tuple<int, int, long double, int, int>(DNF[*it][i].nb_data_recup, DNF[*it][i].stream,
                                                                                                       DNF[*it][i].proba, *it, i));
                    }
                }
            }
            
            // Call to the greedy algorithm that optimally schedules the leaves of a single AND
            int leaf_rest = nb_leaves_per_and[*it];
            cost = prec_bestcost;
            opt_single_and(DNF, nb_streams, nb_ands, nb_leaves_per_and, streamCost,
                       leaf_rest, cost, disjoint_set, final_order);
            
            // Depending on the considered heuristic, the objective function is evaluated for the considered AND
            if(heur==1){
                ratio = (cost - prec_bestcost) / proba_and[*it];
            }
            
            if(heur==2){
                ratio = (cost - prec_bestcost);
                
            }
            
            if(heur==3){
                ratio = 1/proba_and[*it];
            }
            
            if (DEBUG1)
            {
                cout << "cost: " << (cost - prec_bestcost)
                << " , andj: " << *it << endl;
                cout << "Ratio of or: " << ratio << endl;
            }
            
            if (ratio < min)
            {
                min = ratio;
                bestand = *it;
                optimal_leaf_order = final_order;
                bestcost = cost;
            }
            
            // Re-initialization of the data-structure
            disjoint_set = vector<multiset<Feuille> > ();
            if (DEBUG1)
            {
                cout << "Completion of processing of  AND:" << *it << endl;
            }
        }
        
        // Update of the list of remaining ANDs
        multiset<int>::iterator it1;
        it1 = and_rest.find(bestand);
        and_rest.erase(it1);
        evaluation_order = optimal_leaf_order;
        if (DEBUG1)
        {
            cout << "bestcost : " << bestcost << " ,bestand : " << bestand << endl;
            vector<leaf_place>::iterator it3;
            for (it3 = evaluation_order.begin(); it3 < evaluation_order.end(); it3++)
            {
                cout << " and :" << it3->get<0> () << " leaf_place :"
                << it3->get<1> () << endl;
            }
        }
        eval_andbyand_dynamic_ratio(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and,
                              nb_streams, bestcost, and_rest, evaluation_order, heur);
    }
    //
    // Else, all ANDs have been scheduled
    //
    else
    {
        if(DEBUG2){
            vector<leaf_place>::iterator it4;
            for (it4 = evaluation_order.begin(); it4 < evaluation_order.end(); it4++)
            {
                cout << " and :" << it4->get<0> () << " leaf_place :"
                << it4->get<1> () << endl;
            }
        }
        bestcost = Cost(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order);
        if(DEBUG2){
            cout << "################## bestcost ############################# "
            << bestcost << endl;
        }
    }
}

//
// And-by-and DYNAMIC greedy heuristic sorting ANDs by the ratio Cost / proba
//
void
eval_andbyand_dynamic_by_c_over_p(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                      long double * streamCost, vector<long double> proba_and, int nb_streams,
                      long double & bestcost1){
	// Data structure to store the set of not yet scheduled ANDs
	multiset<int> and_rest;
	for (int j = 0; j < nb_ands; j++)
	{
		and_rest.insert(j);
	}
	// Data structure to store the leaf order
	vector<leaf_place> evaluation_order;

    if(DEBUG2){
        cout << "*************Start of eval_andbyand_by_c_over_p*********************** "<<endl;
    }
    eval_andbyand_dynamic_ratio(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost1, and_rest, evaluation_order, 1);
    if(DEBUG2){
        cout << "*************End of eval_andbyand_by_c_over_p*********************** "<<endl;
    }
}

//
// And-by-and DYNAMIC greedy heuristic sorting ANDs by the Cost
//
void
eval_andbyand_dynamic_bycost(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                     long double * streamCost, vector<long double> proba_and, int nb_streams,
                     long double & bestcost2)
{
	// Data structure to store the set of not yet scheduled ANDs
	multiset<int> and_rest;
	for (int j = 0; j < nb_ands; j++)
	{
		and_rest.insert(j);
	}
	// Data structure to store the leaf order
	vector<leaf_place> evaluation_order;

    if(DEBUG2){
        cout    << "*************Start of eval_andbyand_bycost***********************"<<endl;
    }
    eval_andbyand_dynamic_ratio(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost2,
    		and_rest, evaluation_order, 2);
    if(DEBUG2){
        cout    << "*************End of eval_andbyand_bycost*********************** "<<endl;
    }
}
//
// And-by-and DYNAMIC greedy heuristic sorting ANDs by decreasing proba
//
void
eval_andbyand_dynamic_bydecreasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                                long double * streamCost, vector<long double> proba_and, int nb_streams,
                                long double & bestcost3)
{
	// Data structure to store the set of not yet scheduled ANDs
	multiset<int> and_rest;
	for (int j = 0; j < nb_ands; j++)
	{
		and_rest.insert(j);
	}
	// Data structure to store the leaf order
	vector<leaf_place> evaluation_order;

    if(DEBUG2){
        cout    << "*************Start of eval_andbyand_bydecreasingproba***********************"<<endl;
    }
    eval_andbyand_dynamic_ratio(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost3,
    		and_rest, evaluation_order, 3);
    if(DEBUG2){
        cout    << "*************End of eval_andbyand_bydecreasingproba*********************** "<<endl;
    }
}

//
// Generic driver for the leaf ordering heuristics
// (these are heuristics that ignore the structure of ANDs)
//
long double
orderleaves_byratio(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                   long double * streamCost, vector<leaf_place> & evaluation_order, long double heur)
{
    long double cost = 0;
    long double bestcost = 0;
    multiset<ratio_leaf> leaves_final_order;
    long double ratio = 1;
    
    // Computation of the cost of each leaf, and of its value for the targeted objective function
    for (int j = 0; j < nb_ands; j++)
    {
        for (int i = 0; i < nb_leaves_per_and[j]; i++)
        {
            cost = DNF[j][i].nb_data_recup*streamCost[DNF[j][i].stream];
            
            if(heur==4){
                ratio = cost / (1 - DNF[j][i].proba);
            }
            if(heur==5){
                ratio = cost / (DNF[j][i].proba);
            }
            if(heur==6){
                ratio = cost;
            }
            if(heur==7){
                ratio = 1/DNF[j][i].proba;
            }
            if(heur==8){
                ratio = DNF[j][i].proba;
            }
            if (DEBUG)
            {
                cout << " and :" << j << " leaf_place :" << i;
                cout << " , cost:" << cost << " ratio:" << ratio << endl;
            }
            // The leaves are stored in a multiset whose first element is the value of the leaf for the targeted
            // objective function. Therefore, the first element retrieved from this data structure is the one with minimal
            // value for the objective function, and so on.
            leaves_final_order.insert(ratio_leaf(ratio, j, i));
        }
    }
    // The leaf ordering is copied into a vector
    for (multiset<ratio_leaf>::iterator it = leaves_final_order.begin(); it != leaves_final_order.end(); it++)
    {
        evaluation_order.push_back(leaf_place(it->get<1> (), it->get<2> ()));
        
        if(DEBUG2)
        {
        	cout << it->get<0> ();
            cout << " and :" << it->get<1> () << " leaf_place :" << it->get<2> ()
            << endl;
        }
        
    }
    // The cost of the solution is evaluated
    bestcost = Cost(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order);
    if(DEBUG2){
        cout << "# bestcost : "<< bestcost << endl;
    }
    return (bestcost);
}


//
// Heuristic ordering leaves by the ratio: cost / (1-proba)
//
long double
orderleaves_by_c_over_q(leaf ** DNF, int nb_ands, int * nb_leaves_per_and, long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_by_c_over_q :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order, 4);
    if(DEBUG2){
        cout << " ***** End of heuristic orderleaves_by_c_over_q :" << endl;
    }
    return (bestcost);
}
//
// Heuristic ordering leaves by the ratio: cost / proba
//
long double
orderleaves_by_c_over_p(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                   long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_byc_over_p :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order, 5);
    if(DEBUG2){
        cout << " ***** End of heuristic orderleaves_byc_over_p****" << endl;
    }
    return (bestcost);
}
//
// Heuristic ordering leaves by cost
//
long double
orderleaves_bycost(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                  long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_bycost :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order, 6);
    if(DEBUG2){
        cout << " ***** End of heuristic orderleaves_bycost****" << endl;
    }
    return (bestcost);
}
//
// Heuristic ordering leaves by decreasing proba
//
long double
orderleaves_bydecreasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                             long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_bydecreasingproba :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order, 7);
    if(DEBUG2){
        cout << " ***** End of heuristic orderleaves_bydecreasingproba****" << endl;
    }
    return (bestcost);
}
//
// Heuristic ordering leaves by increasing proba
//
long double
orderleaves_byincreasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                             long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_byincreasingproba :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order, 8);
    if(DEBUG2){cout << " ***** End of heuristic orderleaves_byincreasingproba****" << endl;
    }
    return (bestcost);
}
//
// Random ordering of the leaves
//
long double order_leaves_randomly(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                             long double * streamCost){
	// Counting the number of leaves in the entire DNF
	int nb_leaves = 0;
	for(int and_id=0; and_id<nb_ands; and_id++){
		nb_leaves += nb_leaves_per_and[and_id];
	}
	// Structure to go from a global index to a local one
	int * global2local_and  = new int [nb_leaves];
	int * global2local_leaf = new int [nb_leaves];
	int leaf_rank = 0;
	for(int and_id=0; and_id<nb_ands; and_id++){
		for(int leaf_id=0; leaf_id<nb_leaves_per_and[and_id]; leaf_id++){
			global2local_and[leaf_rank]  = and_id;
			global2local_leaf[leaf_rank] = leaf_id;
			leaf_rank++;
		}
	}

	// Initialization of the array that will contain the permutation of the leaves
	int * random_leaf_order = new int [nb_leaves];
	for(int leaf_id=0; leaf_id<nb_leaves; leaf_id++){
		random_leaf_order[leaf_id] = leaf_id;
	}
	// Generation of the permutation
	std::srand ( unsigned ( std::time(0) ) );
	random_shuffle(random_leaf_order, random_leaf_order+nb_leaves);
	if(DEBUG){
		cout << "Random leaf order: ";
		for(int leaf_id=0; leaf_id<nb_leaves; leaf_id++){
			cout << random_leaf_order[leaf_id] << "\t";
		}
		cout << endl;
	}
	// Copying the permutation in the right data structure and then evaluating the cost of that permutation
	vector<leaf_place> leaf_order;
	for(int leaf_id = 0; leaf_id<nb_leaves; leaf_id++){
//		leaf_order.push_back(leaf_place(global2local_and[leaf_rank], global2local_leaf[leaf_rank]));
		leaf_order.push_back(leaf_place(global2local_and[random_leaf_order[leaf_id]], global2local_leaf[random_leaf_order[leaf_id]]));
	}
	long double cost = Cost(DNF, nb_ands, nb_leaves_per_and, streamCost, leaf_order);

	delete [] global2local_leaf;
	delete [] global2local_and;
	delete [] random_leaf_order;

	return cost;
}
//
// Stream ordering heuristic from the Lim, Misra, and Mo paper
//
bool stream_lipyeow_sorter(stream_lipyeow const& lhs, stream_lipyeow const& rhs) {
	return lhs.gain > rhs.gain;
}
bool increasing_elements_sorter(leaf4lipyeow const& lhs, leaf4lipyeow const& rhs) {
	return lhs.n_elements < rhs.n_elements;
}
bool decreasing_elements_sorter(leaf4lipyeow const& lhs, leaf4lipyeow const& rhs) {
	return lhs.n_elements > rhs.n_elements;
}
long double Lipyeow_ordering(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                             long double * streamCost, int nb_streams,
                             bool decreasing_sort){
	// Computation of the total number of leaves
	int  nb_total_leaves = 0;
	for(int and_rank=0; and_rank<nb_ands; and_rank++){
		nb_total_leaves += nb_leaves_per_and[and_rank];
	}
	// Data structure to record the largest requirement for each stream
	stream_lipyeow * stream_gains = new stream_lipyeow[nb_streams];
	// Data structure to record which leaf requires data from which stream
	int * streams_to_nb_leaves = new int [nb_streams];
	leaf4lipyeow ** streams_to_leaves = new leaf4lipyeow * [nb_streams];
	for(int i=0; i<nb_streams; i++){
		streams_to_leaves[i] = new leaf4lipyeow [nb_total_leaves];
		streams_to_nb_leaves[i] = 0;
	}
	// Initializations
	for(int i=0; i<nb_streams; i++){
		stream_gains[i].used = false;
		stream_gains[i].n_elements = 0;
		stream_gains[i].gain = 0;
		stream_gains[i].stream_id = i;
	}
	// Computing the gains while identifying the leaves reading the most elements of each stream
	for(int and_rank=0; and_rank<nb_ands; and_rank++){
		for(int leaf_rank=0; leaf_rank<nb_leaves_per_and[and_rank]; leaf_rank++){
			int stream_id = DNF[and_rank][leaf_rank].stream;
			if (stream_gains[stream_id].n_elements < DNF[and_rank][leaf_rank].nb_data_recup){
				stream_gains[stream_id].n_elements = DNF[and_rank][leaf_rank].nb_data_recup	;
				stream_gains[stream_id].and_id  = and_rank;
				stream_gains[stream_id].leaf_id = leaf_rank;
			}
			stream_gains[stream_id].gain += (1-DNF[and_rank][leaf_rank].proba)*nb_leaves_per_and[and_rank];
			stream_gains[stream_id].used = true;
			streams_to_leaves[stream_id][streams_to_nb_leaves[stream_id]].and_id = and_rank;
			streams_to_leaves[stream_id][streams_to_nb_leaves[stream_id]].leaf_id = leaf_rank;
			streams_to_leaves[stream_id][streams_to_nb_leaves[stream_id]].n_elements = DNF[and_rank][leaf_rank].nb_data_recup;
			streams_to_leaves[stream_id][streams_to_nb_leaves[stream_id]].stream_id = stream_id;
			streams_to_nb_leaves[stream_id]++;
		}
	}
	for(int i=0; i<nb_streams; i++){
		if(stream_gains[i].used){
			stream_gains[i].gain = stream_gains[i].gain/(stream_gains[i].n_elements*streamCost[i]);
		}
	}
	// Sanity check
	int nb_leaves_stored = 0;
	for(int i=0; i<nb_streams; i++){
		nb_leaves_stored += streams_to_nb_leaves[i];
	}
	assert(nb_leaves_stored == nb_total_leaves);
	// Sorting the streams
	std::sort(stream_gains, stream_gains+nb_streams, &stream_lipyeow_sorter);
	// Building the leaf ordering
	int * Order_AndIds = new int [nb_total_leaves];
	int * Order_LeavesIds = new int [nb_total_leaves];
	int nb_sorted_leaves = 0;
	for(int i=0; i<nb_streams; i++){
		if(stream_gains[i].used){
			int stream_id = stream_gains[i].stream_id;
			if (decreasing_sort){
				std::sort(streams_to_leaves[stream_id], streams_to_leaves[stream_id]+streams_to_nb_leaves[stream_id], &decreasing_elements_sorter);
			}
			else{
				std::sort(streams_to_leaves[stream_id], streams_to_leaves[stream_id]+streams_to_nb_leaves[stream_id], &increasing_elements_sorter);
			}
			for(int leaf_id = 0; leaf_id<streams_to_nb_leaves[stream_id]; leaf_id++){
				Order_AndIds[nb_sorted_leaves]    = streams_to_leaves[stream_id][leaf_id].and_id;
				Order_LeavesIds[nb_sorted_leaves] = streams_to_leaves[stream_id][leaf_id].leaf_id;
				nb_sorted_leaves ++;
			}
		}
	}
	// Sanity scheck
	assert(nb_sorted_leaves == nb_total_leaves);
	// Evaluating the cost of the leaf ordering
	long double cost = Cost4Arrays(DNF, nb_ands, nb_leaves_per_and, streamCost,
			nb_sorted_leaves, Order_AndIds, Order_LeavesIds);

	delete [] stream_gains;
	delete [] streams_to_nb_leaves;
	for(int i=0; i<nb_streams; i++){
		delete [] streams_to_leaves[i];
	}
	delete [] streams_to_leaves;
	delete [] Order_AndIds;
	delete [] Order_LeavesIds;
	return cost;
}

//
// Generic driver for the and-by-and STATIC heuristics
//
void
order_andbyand_static_ratio(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                  long double * streamCost, vector<long double> proba_and, int nb_streams,
                  long double & bestcost,
                  int heur)
{
	// Data structure to store the set of not yet scheduled ANDs
	multiset<int> and_rest;
	for (int j = 0; j < nb_ands; j++)
	{
		and_rest.insert(j);
	}
	// Ordered data structure to store the objective values of the different ANDs
	multiset<ratio_and> and_final_order;
	// Data structure to store the leaf order for each AND
	vector<leaf_place> initleaf_place;
	vector<vector<leaf_place> > leaf_order(nb_ands, (initleaf_place));
    
    long double cost;
    multiset<int>::iterator it;
    
    long double ratio = 1;
    
    if( DEBUG2 ) {
        multiset<int>::iterator it0;
        for (it0 = and_rest.begin(); it0 != and_rest.end(); it0++)
        {
            
            cout << *it0 << " , ";
        }
        cout << endl;
    }

    // Loop over the ANDs
    for (it = and_rest.begin(); it != and_rest.end(); it++)
    {
    	// Data structure to hold, for each stream, the multiset of leaves using data from that stream
        multiset<Feuille> myset_feuille;
        std::vector<multiset<Feuille> > disjoint_set(nb_streams, (myset_feuille));

    	// Initialization of the temporary variables
    	vector<leaf_place> final_order; // = evaluation_order;
        cost = 0;
        
        // We build for each stream the subset of the leaves that use data from it
        for (int i = 0; i < nb_leaves_per_and[*it]; i++)
        {
            for (int s = 0; s < nb_streams; s++)
            {
                if (DNF[*it][i].stream == s)
                {
                    (disjoint_set[s]).insert(boost::tuples::tuple<int, int, long double, int, int>(DNF[*it][i].nb_data_recup, DNF[*it][i].stream,
                                                                                                   DNF[*it][i].proba, *it, i));
                }
            }
        }
        
        int leaf_rest = nb_leaves_per_and[*it];

        // Evaluation of the cost of the execution of the targeted AND
        opt_single_and(DNF, nb_streams, nb_ands, nb_leaves_per_and, streamCost, leaf_rest, cost, disjoint_set, final_order);

        // Depending on the considered heuristic, the objective function is evaluated for the considered AND
        if(heur==9){
            ratio = cost / proba_and[*it];
        }
        if(heur==10){
            ratio = cost;
        }
        if(heur==11){
            ratio =proba_and[*it];
        }
        
        if(heur==12){
            ratio = 1 / proba_and[*it];
        }
        
        if (DEBUG1)
        {
            cout << "cost : " << cost << " , andj : " << *it << endl;
            cout << "Ratio :" << ratio << endl;
        }
        // The ANDs are stored in a multiset whose first element is the value of the AND for the targeted
        // objective function. Therefore, the first element retrieved from this data structure is the one with minimal
        // value for the objective function, and so on.
        and_final_order.insert(ratio_and(ratio, *it));
        // The leaf order for the targeted AND is stored in memory
        leaf_order[*it] = final_order;
        
        // Reinitialization of disjoint_set
        disjoint_set = vector<multiset<Feuille> > ();
        
    }
    
    
    // The entire leaf order is copied in a vector
    vector<leaf_place> evaluation_order;
    for (multiset<ratio_and>::iterator it2 = and_final_order.begin(); it2 != and_final_order.end(); it2++)
    {
        int andj = it2->get<1> ();
        for (vector<leaf_place>::iterator it4 = leaf_order[andj].begin(); it4 != leaf_order[andj].end(); it4++)
        {
            evaluation_order.push_back(leaf_place(it4->get<0> (), it4->get<1> ()));
        }
    }
    if(DEBUG2){
        vector<leaf_place>::iterator it3;
        for (it3 = evaluation_order.begin(); it3 < evaluation_order.end(); it3++)
        {
            cout << " and :" << it3->get<0> () << " leaf_place :" << it3->get<1> ()
            << endl;
        }
    }
    // The cost of the leaf order is computed
    bestcost = Cost(DNF, nb_ands, nb_leaves_per_and, streamCost, evaluation_order);
    if(DEBUG2){
        cout
        << "##bestcost : "<< bestcost << endl;
        
    }
}

//
// And-by-and STATIC greedy heuristic sorting ANDs by the ratio Cost / proba
//
void
order_andbyand_static_by_c_over_p(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                  long double * streamCost, vector<long double> proba_and, int nb_streams,
                  long double & bestcost){
    if(DEBUG2){
        cout
        << "******************** Start of heuristic order_andbyand_static_by_c_over_p*********************** "<< endl;
    }
    order_andbyand_static_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost, 9);
    
    if(DEBUG2){
        cout
        << "******************** End of heuristic order_andbyand_static_by_c_over_p*********************** "<< endl;
    }
}
//
// And-by-and STATIC greedy heuristic sorting ANDs by Cost
//
void
order_andbyand_static_by_cost(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                 long double * streamCost, vector<long double> proba_and, int nb_streams,
                 long double & bestcost)
{if(DEBUG2){
    cout
    << "********************Start of heuristic order_andbyand_static_by_cost*********************** "<< endl;
}
    order_andbyand_static_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost, 10);
    
    if(DEBUG2){
        cout
        << "********************End of heuristic order_andbyand_static_by_cost*********************** "<< endl;
    }
}
//
// And-by-and STATIC greedy heuristic sorting ANDs by increasing proba
//
void
order_andbyand_static_by_increasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                            long double * streamCost, vector<long double> proba_and, int nb_streams,
                            long double & bestcost)
{
    if(DEBUG2){
        cout
        << "******************** Start of heuristic order_andbyand_static_by_increasingproba*********************** "<< endl;
        
    }
    order_andbyand_static_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost, 11);
    
    if(DEBUG2){
        cout
        << "******************** End of heuristic order_andbyand_static_by_increasingproba*********************** "<< endl;
    }
}
//
// And-by-and STATIC greedy heuristic sorting ANDs by decreasing proba
//
void
order_andbyand_static_by_decreasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                            long double * streamCost, vector<long double> proba_and, int nb_streams,
                            long double & bestcost)
{
    if(DEBUG2){
        cout
        << "********************Start of heuristic order_andbyand_static_by_decreasingproba*********************** "<< endl;
    }
    order_andbyand_static_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, bestcost, 12);
    
    if(DEBUG2){
        cout
        << "********************End of heuristic order_andbyand_static_by_decreasingproba*********************** "<< endl;
    }
}
//
// Function to evaluate the cost of a leaf ordering specified as a vector
//
long double
Cost(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, long double * streamCost,
     vector<leaf_place> evaluation_order)
{
    
    //Declaration of all data structures needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
    int nb_data_recup;
    int stream;
    long double proba;
    int And_eval;
    vector<leaf_place>::iterator it;

    // Data structure to memorize which ANDs have all their leaves already evaluated
    bool * andCompleted = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        andCompleted[k] = false;
    }
    // Data structure to record which ANDs need the data item considered
    bool * Needingand = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        Needingand[k] = false;
    }
    // To record whether the considered stream is needed or not
    int Need_stream = 0;
    // To record the first leaf (according to the execution order) of each AND which requires the considered data
    int * minleaf = new int[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        minleaf[k] = -1;
    }
    
    long double * probaAndTrue = new long double[nb_ands];
    long double probaPrecendentLeavesTrue = 1;
    
    // Initially all the leaves are marked as not yet visited / evaluated
    for (int k = 0; k < nb_ands; k++)
    {
        for (int i = 0; i < nb_leaves_per_and[k]; i++)
        {
            DNFTree[k][i].full_eval = 0;
        }
    }
    
    // The leaf order is copied from the vector description into the DNF data structure
    int ind = -1;
    for (it = evaluation_order.begin(); it < evaluation_order.end(); it++)
    {
        ind++;
        DNFTree[it->get<0> ()][it->get<1> ()].eval_order = ind;
    }
    
    // Loop on all the leaves, in their evaluation order, to compute the overall cost of the leaf ordering
    for (it = evaluation_order.begin(); it < evaluation_order.end(); it++)
    {
        // Initialization of the variables relative to the considered leaf
        Leaf_cost = 0;
        if (DEBUG == 1)
        {
            cout << "Feuille with and :" << it->get<0> () << "  and leaf_place :"
            << it->get<1> () << endl;
        }
        nb_data_recup = DNFTree[it->get<0> ()][it->get<1> ()].nb_data_recup;
        stream = DNFTree[it->get<0> ()][it->get<1> ()].stream;
        proba = DNFTree[it->get<0> ()][it->get<1> ()].proba;
        
        // Computing the probability that all leaves preceding the considered leaf in its AND evaluate to true
        probaPrecendentLeavesTrue = 1;
        for (int i = 0; i < nb_leaves_per_and[it->get<0> ()]; i++)
        {
            if (DNFTree[it->get<0> ()][i].full_eval == 1)
            {
                probaPrecendentLeavesTrue = probaPrecendentLeavesTrue
                * DNFTree[it->get<0> ()][i].proba;
            }
        }
        if (DEBUG == 1)
        {
            cout << "probaPrecendentLeavesTrue : " << probaPrecendentLeavesTrue
            << endl;
        }
        
        int nb_recup = 0;
        // Loop on all the elements required by the considered leaf
        for (int e = 0; e < nb_data_recup; e++)
        {
            nb_recup++;
            // Check which ANDs have already been completed, which one needs that data,
            // and what is the overall probability of successful evaluation of that AND if its evaluation is complete
            for (int k = 0; k < nb_ands; k++)
            {
                andCompleted[k] = false;
                Needingand[k] = false;
                probaAndTrue[k] = 1;
            }
            
            int found = 0;
            for (int j = 0; j < nb_ands; j++)
            {
                And_eval = 0;
                Need_stream = 0;
                int eval_rank = INT_MAX;
                for (int i = 0; i < nb_leaves_per_and[j]; i++)
                {
                    if (DNFTree[j][i].full_eval == 1)
                    {
                        And_eval++;
                        if (DNFTree[j][i].stream == stream
                            && DNFTree[j][i].nb_data_recup >= nb_recup)
                        {
                            Need_stream = 1;
                            Needingand[j] = true;
                            
                            if(DNFTree[j][i].eval_order < eval_rank){
                            	eval_rank = DNFTree[j][i].eval_order;
                            	minleaf[j] = i;
                            }

                            found = 1;
                        }
                        
                    }
                    probaAndTrue[j] = probaAndTrue[j] * DNFTree[j][i].proba;
                }
                
                
                if ((And_eval == nb_leaves_per_and[j]) && Need_stream == 0)
                    andCompleted[j] = true;
            }
            
            // Computation of the probability of execution of the first leaf in an AND (minleaf[])
            // that requires the considered data element
            long double * probaLeavesPrecedingNeedingOne = new long double[nb_ands];
            for (int k = 0; k < nb_ands; k++)
            {
                probaLeavesPrecedingNeedingOne[k] = 1;
            }
            
            for (int j = 0; j < nb_ands; j++)
            {
                
                if ((Needingand[j] == true) && (j != it->get<0> ()))
                {
                    for (int i = 0; i < nb_leaves_per_and[j]; i++)
                    {
                        if ((DNFTree[j][i].full_eval == 1)
                            && (DNFTree[j][i].eval_order
                                < DNFTree[j][minleaf[j]].eval_order))
                        {
                            
                            probaLeavesPrecedingNeedingOne[j]
                            = probaLeavesPrecedingNeedingOne[j]
                            * DNFTree[j][i].proba;
                        }
                    }//for i
                }
                if (DEBUG == 1)
                {
                    cout << "probaLeavesPrecedingNeedingOne[" << j << "] : "
                    << probaLeavesPrecedingNeedingOne[j] << endl;
                }
            }//for j
            
            
            long double probaCompletedAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
                if (andCompleted[j] == true)
                {
                    probaCompletedAndsFalse = probaCompletedAndsFalse * (1 - probaAndTrue[j]);
                }
            }
            if (DEBUG == 1)
            {
                cout << " probaCompletedAndsFalse :" << probaCompletedAndsFalse
                << endl;
            }
            
            long double probaNeedingAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
                if ((Needingand[j] == true) && (j != it->get<0> ()))
                {
                    probaNeedingAndsFalse = probaNeedingAndsFalse * (1 - probaLeavesPrecedingNeedingOne[j]);
                }
            }
            if (DEBUG == 1)
            {
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }
            delete [] probaLeavesPrecedingNeedingOne;
            
            // If the considered element is not the input of any preceding leaf
            if (found == 0)
            {
                Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeavesTrue * streamCost[stream];
                if (DEBUG == 1)
                {
                    cout << "found: " << found << ", probaPrecendentLeavesTrue: "
                    << probaPrecendentLeavesTrue << ", leafcost: "
                    << probaCompletedAndsFalse * probaPrecendentLeavesTrue
                    * streamCost[stream] << "nb_recup: " << nb_recup
                    << endl;
                }
            }
            
            else
            {
                // Case where the considered element was already loaded by (a preceding leaf of) the AND of the considered leaf
                if (Needingand[it->get<0> ()] == true)
                {
                    Leaf_cost += 0;
                    if (DEBUG == 1)
                    {
                        cout << "found :" << found << " ,leafcost :" << 0
                        << "nb_recup :" << nb_recup << endl;
                    }
                }
                // Case where the element could have been loaded by other ANDs, but not the one containing the considred leaf
                else
                {
                    Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeavesTrue) * streamCost[stream];
                    if (DEBUG == 1)
                    {
                        cout << "found: " << found << ", leafcost: "
                        << probaNeedingAndsFalse * (probaCompletedAndsFalse
                                                    * probaPrecendentLeavesTrue) * streamCost[stream]
                        << ", nb_recup: " << nb_recup << endl;
                    }
                }
            }
        }
        
        DNFTree[it->get<0> ()][it->get<1> ()].full_eval = 1;
        Global_cost += Leaf_cost;
    }
    
    delete [] probaAndTrue;
    delete [] minleaf;
    delete [] Needingand;
    delete [] andCompleted;

    return (Global_cost);
}
//
// Function to evaluate the cost of a leaf ordering specified by an array description rather than on a vector description
//
long double
Cost4Arrays(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, long double * streamCost,
		int nb_leaves, int * and_id, int * leaf_id)
{
    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
    int nb_data_recup;
    int stream;
    long double proba;
    int nb_leaves_evaluated;

    // Data structure to record the probability of execution of the first leaf in an AND (minleaf[])
    // that requires the considered data element
    long double * probaLeavesPrecedingNeedingOne = new long double[nb_ands];
    // Data structure to memorize which ANDs have all their leaves already evaluated
    bool * andCompleted = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        andCompleted[k] = false;
    }
    // Data structure to record which ANDs need the data item considered
    bool * Needingand = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        Needingand[k] = false;
    }
    // To record whether the considered stream is needed or not
    int Need_stream = 0;
    // To record the first leaf (according to the execution order) of each AND which requires the considered data
    int * minleaf = new int[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        minleaf[k] = -1;
    }

    long double * probaAndTrue = new long double[nb_ands];
    long double probaPrecendentLeavesTrue = 1;

    // Initially all the leaves are marked as not yet visited / evaluated
    for (int k = 0; k < nb_ands; k++)
    {
        for (int i = 0; i < nb_leaves_per_and[k]; i++)
        {
            DNFTree[k][i].full_eval = 0;
        }
    }

    // The rank of each leaf is stored in the DNF data structure
    // It is computed from the evaluation order given as argument to the function
    for(int i=0; i<nb_leaves; i++){
    	DNFTree[and_id[i]][leaf_id[i]].eval_order = i;
    }

    // Computation of the global cost
    // We compute the cost induced by each leaf, considering leaves one by one in the evaluation order
    for(int leaf_rank=0; leaf_rank<nb_leaves; leaf_rank++)
    {
    	// Retrieval of the identity and characteristics of the ``target'' leaf
        int the_and = and_id[leaf_rank];
        int the_leaf = leaf_id[leaf_rank];
        nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup;
        stream = DNFTree[the_and][the_leaf].stream;
        proba = DNFTree[the_and][the_leaf].proba;
        // Initialization of the leaf cost
        Leaf_cost = 0;

        if (DEBUG == 1)
        {
            cout << "Feuille with and :" << the_and << "  and leaf_place :"
            << the_leaf << endl;
        }

        // If the AND the target leaf belongs to is evaluated, computation of the probability that the target leaf itself is evaluated
        // This is the product of the probability of success of this AND leaves that are executed (in the order) before the target leaf
        probaPrecendentLeavesTrue = 1;
        for (int i = 0; i < nb_leaves_per_and[the_and]; i++)
        {
            if (DNFTree[the_and][i].full_eval == 1)
            {
                probaPrecendentLeavesTrue *= DNFTree[the_and][i].proba;
            }
        }
        if (DEBUG == 1)
        {
            cout << "probaPrecendentLeavesTrue : " << probaPrecendentLeavesTrue
            << endl;
        }

        // We consider one by one all the input data elements the target leaf depends upon
        int nb_recup = 0;
        for (int e = 0; e < nb_data_recup; e++)
        {
            nb_recup++;
            // Initializations...
            for (int k = 0; k < nb_ands; k++)
            {
                andCompleted[k] = false;
                Needingand[k] = false;
                probaAndTrue[k] = 1;
            }

            int found = 0;
            // Loop on all the ANDs
            for (int j = 0; j < nb_ands; j++)
            {
                nb_leaves_evaluated = 0;
                Need_stream = 0;
                int eval_rank = INT_MAX;
                // Loop on all the leaves of the considered AND
                for (int i = 0; i < nb_leaves_per_and[j]; i++)
                {
                	// If the leaf had been evaluated = precedes (directly or not) the target leaf in the evaluation order
                	if (DNFTree[j][i].full_eval == 1)
                    {
                        nb_leaves_evaluated++;
                        // If the considered leaf requires the considered element of the target leaf
                        if (DNFTree[j][i].stream == stream
                            && DNFTree[j][i].nb_data_recup >= nb_recup)
                        {
                        	// The considered AND is marked as requiring the considered data input element
                        	Need_stream = 1;
                            Needingand[j] = true;
                            // The characteristics of the leaf are recorded if this is (so far) the first leaf of this AND,
                            // in the evaluation order, that requires the considered input data element.
                            if(DNFTree[j][i].eval_order < eval_rank){
                            	eval_rank = DNFTree[j][i].eval_order;
                            	minleaf[j] = i;
                            }

                            found = 1;
                        }
                    }
                	// Computing the overall probability of success of the evaluation of the considered AND
                    probaAndTrue[j] *= DNFTree[j][i].proba;
                }

                // If all the leaves in the AND where evaluated and if this AND did not require the considered input data element, the AND is marked as completed
                if ((nb_leaves_evaluated == nb_leaves_per_and[j]) && Need_stream == 0)
                    andCompleted[j] = true;
            }

            // Computation of the probability of success of the leaves that precede the minleaf in its own AND
            // The minleaf is the FIRST leaf (in the evaluation order) in the AND that requires the considered input data element
            for (int k = 0; k < nb_ands; k++)
            {
                probaLeavesPrecedingNeedingOne[k] = 1;
            }

            // Loop over all the ANDs
            for (int j = 0; j < nb_ands; j++)
            {
            	// If the considered AND is not the AND including the target leaf, but if it requires the considered input data element
                if ((Needingand[j] == true) && (j != the_and))
                {
                	// Loop over all the leaves of the considered AND
                	for (int i = 0; i < nb_leaves_per_and[j]; i++)
                    {
                		// If the leaf was evaluated, and preceded the minleaf
                		if ((DNFTree[j][i].full_eval == 1)
                            && (DNFTree[j][i].eval_order
                                < DNFTree[j][minleaf[j]].eval_order))
                        {
                            probaLeavesPrecedingNeedingOne[j] *= DNFTree[j][i].proba;
                        }
                    }//for i
                }
                if (DEBUG == 1)
                {
                    cout << "probaLeavesPrecedingNeedingOne[" << j << "] : "
                    << probaLeavesPrecedingNeedingOne[j] << endl;
                }
            }//for j


            // Compute the probability that all ANDs completely evaluated and not requiring the considered input data elements were all false
            long double probaCompletedAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
                if (andCompleted[j] == true)
                {
                    probaCompletedAndsFalse *= (1 - probaAndTrue[j]);
                }
            }
            if (DEBUG == 1)
            {
                cout << " probaCompletedAndsFalse :" << probaCompletedAndsFalse
                << endl;
            }

            // Probability that none of the preceding leaves requiring the input data element were evaluated
            long double probaNeedingAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
                if ((Needingand[j] == true) && (j != the_and))
                {
                    probaNeedingAndsFalse *= (1 - probaLeavesPrecedingNeedingOne[j]);
                    if (DEBUG) cout << "\t\t\t" << probaLeavesPrecedingNeedingOne[j] << " (" << j << ")" << endl;
                }
            }

            if (DEBUG == 1)
            {
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }

            // If none of the preceding leaves required the considered input data element
            if (found == 0)
            {
                Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeavesTrue * streamCost[stream];
                if (DEBUG)
                cout << "\tNF\t" << probaCompletedAndsFalse << "*" << probaPrecendentLeavesTrue << endl;
                if (DEBUG == 1)
                {
                    cout << "found :" << found << " ,probaPrecendentLeavesTrue :"
                    << probaPrecendentLeavesTrue << " ,leafcost :"
                    << probaCompletedAndsFalse * probaPrecendentLeavesTrue
                    * streamCost[stream] << "nb_recup :" << nb_recup
                    << endl;
                }
            }
            else
            {
            	// One of the leaves of the AND including the target leaf, and preceding the target leaf in the evaluation order, required the considered input data element
            	// Therefore, each time the target leaf is evaluated the require input data element has always been loaded and the cost is null.
                if (Needingand[the_and] == true)
                {
                    Leaf_cost += 0;
                    if (DEBUG)
                    	cout << "\t0" << endl;
                    if (DEBUG == 1)
                    {
                        cout << "found :" << found << " ,leafcost :" << 0
                        << "nb_recup :" << nb_recup << endl;
                    }
                }
                // The remaining case: the considered input data element could have been loaded by at least one AND, but not by the one including the target leaf
                else
                {
                    Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeavesTrue) * streamCost[stream];
                    if (DEBUG)
                    cout << "\tF\t" << probaNeedingAndsFalse << "*" << probaCompletedAndsFalse << "*" << probaPrecendentLeavesTrue << endl;
                    if (DEBUG == 1)
                    {
                        cout << "found :" << found << " ,leafcost :"
                        << probaNeedingAndsFalse * (probaCompletedAndsFalse
                                                    * probaPrecendentLeavesTrue) * streamCost[stream]
                        << " ,nb_recup :" << nb_recup << endl;
                    }
                }
            }
        }

        // We mark the considered leaf as have been evaluated
        DNFTree[the_and][the_leaf].full_eval = 1;
        // We add the cost of the target leaf to the global cost computed so far
        Global_cost += Leaf_cost;
        if (DEBUG)
        cout<<"!!!!!!!Global_cost :"<<Global_cost << " (" << Leaf_cost << ")" << endl;

    }

    delete [] probaLeavesPrecedingNeedingOne;
    delete [] probaAndTrue;
    delete [] minleaf;
    delete [] Needingand;
    delete [] andCompleted;
    return (Global_cost);
}


// Optimized version of the above function
long double
Cost4Arrays_optimized(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, long double * streamCost,
		int nb_leaves, int * and_id, int * leaf_id)
{
    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
    int nb_data_recup;
    int stream;
    long double proba;

    // Data structure to record how leaves of each AND have been evaluated so far
    // and which ANDs have been fully evaluated so far
    int  * nb_evaluated_leaves = new int [nb_ands];
    bool * andCompleted = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++){
    	nb_evaluated_leaves[k] = 0;
        andCompleted[k] = false;
    }

    // Computing the number of considered streams
    int nb_streams = 1;
    for(int AND_rank = 0; AND_rank < nb_ands; AND_rank++){
    	for(int leaf_rank=0; leaf_rank < nb_leaves_per_and[AND_rank]; leaf_rank++){
    		if (nb_streams < 1+DNFTree[AND_rank][leaf_rank].stream){
    			nb_streams = 1+DNFTree[AND_rank][leaf_rank].stream;
    		}
    	}
    }
    // Data structure to record the maximum number of elements per stream
    int * max_elements_per_stream = new int [nb_streams];
    for(int stream_id=0; stream_id<nb_streams; stream_id++){
    	max_elements_per_stream[stream_id] = 0;
    }
    for(int AND_rank = 0; AND_rank < nb_ands; AND_rank++){
    	for(int leaf_rank=0; leaf_rank < nb_leaves_per_and[AND_rank]; leaf_rank++){
    		if(max_elements_per_stream[DNFTree[AND_rank][leaf_rank].stream] < DNFTree[AND_rank][leaf_rank].nb_data_recup){
    			max_elements_per_stream[DNFTree[AND_rank][leaf_rank].stream] = DNFTree[AND_rank][leaf_rank].nb_data_recup;
    		}
    	}
    }
    // Data structure to record which data input elements have already been encountered
    bool ** found = new bool * [nb_streams];
	for(int stream_id=0; stream_id<nb_streams; stream_id++){
		found[stream_id] = new bool [max_elements_per_stream[stream_id]];
		for(int nb_streams_elements=0; nb_streams_elements < max_elements_per_stream[stream_id]; nb_streams_elements++){
			found[stream_id][nb_streams_elements] = false;
		}
	}
    // Data structure to record whether any input data item has already been encountered in preceding leaves
    bool *** AND_needs_data = new bool ** [nb_ands];
    long double *** proba_data_read = new long double ** [nb_ands];
    for(int AND_rank = 0; AND_rank < nb_ands; AND_rank++){
    	AND_needs_data[AND_rank] = new bool * [nb_streams];
    	proba_data_read[AND_rank] = new long double * [nb_streams];
    	for(int stream_id=0; stream_id<nb_streams; stream_id++){
        	AND_needs_data[AND_rank][stream_id] = new bool [max_elements_per_stream[stream_id]];
        	proba_data_read[AND_rank][stream_id] = new long double [max_elements_per_stream[stream_id]];
    		for(int nb_streams_elements=0; nb_streams_elements < max_elements_per_stream[stream_id]; nb_streams_elements++){
    			AND_needs_data[AND_rank][stream_id][nb_streams_elements] = false;
    			proba_data_read[AND_rank][stream_id][nb_streams_elements] = 0;
    		}
    	}
    }
    delete [] max_elements_per_stream;

    // Computation of each AND to evaluate to true
    long double * probaAndTrue = new long double[nb_ands];
    for (int k = 0; k < nb_ands; k++){
    	probaAndTrue[k] = 1;
    }
    // Data structure to record the probability that a leaf is executed, only taking its including AND into account
    long double ** proba_leaf_evaluated = new long double * [nb_ands];
    for(int AND_rank = 0; AND_rank < nb_ands; AND_rank++){
    	proba_leaf_evaluated[AND_rank] = new long double [nb_leaves_per_and[AND_rank]];
    	for(int leaf_rank=0; leaf_rank < nb_leaves_per_and[AND_rank]; leaf_rank++){
    		proba_leaf_evaluated[AND_rank][leaf_rank] = 1;
    	}
    }
    // Loop over all the leaves in the evaluation order
    for(int leaf_rank=0; leaf_rank<nb_leaves; leaf_rank++)
       {
       	// Retrieval of the identity and characteristics of the ``target'' leaf
           int the_and = and_id[leaf_rank];
           int the_leaf = leaf_id[leaf_rank];
           proba_leaf_evaluated[the_and][the_leaf] = probaAndTrue[the_and];
           probaAndTrue[the_and] *= DNFTree[the_and][the_leaf].proba;
       }

    long double probaPrecendentLeavesTrue = 1;

    // The full_eval field of each leaf is initialized to 0
    for (int k = 0; k < nb_ands; k++){
        for (int i = 0; i < nb_leaves_per_and[k]; i++){
            DNFTree[k][i].full_eval = 0;
        }
    }

    // The rank of each leaf is stored in the DNF datavstructure
    // It is computed from the evaluation order given as argument to the function
    for(int i=0; i<nb_leaves; i++){
    	DNFTree[and_id[i]][leaf_id[i]].eval_order = i;
    }

    // Computation of the global cost
    // We compute the cost induced by each leaf, considering leaves one by one in the evaluation order
    for(int leaf_rank=0; leaf_rank<nb_leaves; leaf_rank++)
    {
    	// Retrieval of the identity and characteristics of the ``target'' leaf
        int the_and = and_id[leaf_rank];
        int the_leaf = leaf_id[leaf_rank];
        nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup;
        stream = DNFTree[the_and][the_leaf].stream;
        proba = DNFTree[the_and][the_leaf].proba;
        // Initialization of the leaf cost
        Leaf_cost = 0;

        if (DEBUG == 1)
        {
            cout << "Feuille with and :" << the_and << "  and leaf_place :"
            << the_leaf << endl;
        }

        // We consider one by one all the input data elements the target leaf depends upon
        for (int e = 0; e < nb_data_recup; e++)
        {
            // Compute the probability that all ANDs completely evaluated and not requiring the considered input data elements were all false
            long double probaCompletedAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
            	if ((andCompleted[j] == true)&&(AND_needs_data[j][stream][e] == false)){

                    probaCompletedAndsFalse *= (1 - probaAndTrue[j]);
                }
            }
            if (DEBUG == 1){
                cout << " probaCompletedAndsFalse :" << probaCompletedAndsFalse
                << endl;
            }

            // Probability that none of the preceding leaves requiring the input data element were evaluated
            long double probaNeedingAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
            	if ((AND_needs_data[j][stream][e] == true) && (j != the_and)){
                    probaNeedingAndsFalse *= (1 - proba_data_read[j][stream][e]);
                }
            }

            if (DEBUG == 1){
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }

            probaPrecendentLeavesTrue = proba_leaf_evaluated[the_and][the_leaf];

            // If none of the preceding leaves required the considered input data element
            if (found[stream][e] == false){
                Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeavesTrue * streamCost[stream];
            }
            else
            {
            	// One of the leaves of the AND including the target leaf, and preceding the target leaf in the evaluation order, required the considered input data element
            	// Therefore, each time the target leaf is evaluated the require input data element has always been loaded and the cost is null.
            	if (AND_needs_data[the_and][stream][e] == true){
                    Leaf_cost += 0;
                }
                // The remaining case: the considered input data element could have been loaded by at least one AND, but not by the one including the target leaf
                else
                {
                    Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeavesTrue) * streamCost[stream];
                }
            }
        }

        // We mark the considered leaf as have been evaluated
        DNFTree[the_and][the_leaf].full_eval = 1;
        // We record that the AND loaded the data
        for(int element = 0; element < nb_data_recup; element++){
        	if(AND_needs_data[the_and][stream][element]==false){
            	proba_data_read[the_and][stream][element] = proba_leaf_evaluated[the_and][the_leaf];
        	AND_needs_data[the_and][stream][element] = true;
        	found[stream][element] = true;
        	}
        }
        // We record that one more leaves of this AND was evaluated and we check whether this AND is now fully evaluated
        nb_evaluated_leaves[the_and] ++;
        if(nb_evaluated_leaves[the_and] == nb_leaves_per_and[the_and]){
        	andCompleted[the_and] = true;
        }
        // We add the cost of the target leaf to the global cost computed so far
        Global_cost += Leaf_cost;
    }

    for(int i=0; i<nb_ands; i++){
    	for(int j=0; j<nb_streams; j++){
    		delete [] AND_needs_data[i][j];
    		delete [] proba_data_read[i][j];
    	}
    	delete [] AND_needs_data[i];
		delete [] proba_data_read[i];
    	delete [] proba_leaf_evaluated[i];
    }
	delete [] AND_needs_data;
	delete [] proba_data_read;
	delete [] proba_leaf_evaluated;
    for(int stream_id=0; stream_id < nb_streams; stream_id++){
    	delete [] found[stream_id];
    }
    delete [] found;
    delete [] probaAndTrue;
    delete [] andCompleted;
    delete [] nb_evaluated_leaves;
    return (Global_cost);
}

// Same function as above, but most data are kept from one call to the other in order to avoir recomputations and reevaluations
long double
Cost4Arrays_stripped(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, long double * streamCost,
		int nb_leaves, int rank_first_leaf, int rank_last_leaf, int * and_id, int * leaf_id, int nb_streams, int * max_elements_per_stream,
		bool *** AND_needs_data, long double *** proba_data_read, long double * probaAndTrue, bool * andCompleted)
{
    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
    int nb_data_recup;
    int stream;
    long double proba;

    long double probaPrecendentLeavesTrue = 1;

    // The full_eval field of each leaf is initialized to 0
    for (int k = 0; k < nb_ands; k++){
        for (int i = 0; i < nb_leaves_per_and[k]; i++){
            DNFTree[k][i].full_eval = 0;
        }
    }

    // Computation of the global cost
    // We compute the cost induced by each leaf, considering leaves one by one in the evaluation order
    for(int leaf_rank=rank_first_leaf; leaf_rank<rank_last_leaf; leaf_rank++)
    {
    	// Retrieval of the identity and characteristics of the ``target'' leaf
        int the_and = and_id[leaf_rank];
        int the_leaf = leaf_id[leaf_rank];
        nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup;
        stream = DNFTree[the_and][the_leaf].stream;
        proba = DNFTree[the_and][the_leaf].proba;
        // Initialization of the leaf cost
        Leaf_cost = 0;

        if (DEBUG == 1)
        {
            cout << "Feuille with and :" << the_and << "  and leaf_place :"
            << the_leaf << endl;
        }


        for (int e = 0; e < nb_data_recup; e++){
            // Compute the probability that all ANDs completely evaluated and not requiring the considered input data elements were all false
            long double probaCompletedAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
            	if ((andCompleted[j] == true)&&(AND_needs_data[j][stream][e] == false)){

                    probaCompletedAndsFalse *= (1 - probaAndTrue[j]);
                }
            }
            if (DEBUG == 1){
                cout << " probaCompletedAndsFalse :" << probaCompletedAndsFalse
                << endl;
            }

            // Probability that none of the preceding leaves requiring the input data element were evaluated
            long double probaNeedingAndsFalse = 1;
            bool found = false;
            for (int j = 0; j < nb_ands; j++)
            {
            	if ((AND_needs_data[j][stream][e] == true) && (j != the_and)){
            		found = true;
                    probaNeedingAndsFalse *= (1 - proba_data_read[j][stream][e]);
                    if (DEBUG) cout << "\t\t\t" << proba_data_read[j][stream][e] << " (" << j << ")" << endl;
                }
            }

            if (DEBUG == 1){
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }

    		// One of the leaves of the AND including the target leaf, and preceding the target leaf in the evaluation order, required the considered input data element
    		// Therefore, each time the target leaf is evaluated the require input data element has always been loaded and the cost is null.
            if (AND_needs_data[the_and][stream][e] == true){
            	Leaf_cost += 0;
            	if (DEBUG) cout << "\t" << 0 << endl;
            }
            else{
            	if (found==false){
            		Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeavesTrue * streamCost[stream];
            		if (DEBUG) cout << "\tNF\t" << probaCompletedAndsFalse << "*" << probaPrecendentLeavesTrue << endl;
            	}
            	// The remaining case: the considered input data element could have been loaded by at least one AND, but not by the one including the target leaf
            	else
            	{
            		Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeavesTrue) * streamCost[stream];
            		if (DEBUG) cout << "\tF\t" << probaNeedingAndsFalse << "*" << probaCompletedAndsFalse << "*" << probaPrecendentLeavesTrue << endl;
            	}
            }
        }

        // We mark the considered leaf as have been evaluated
        DNFTree[the_and][the_leaf].full_eval = 1;
        // We record that the AND loaded the data
        for(int element = 0; element < nb_data_recup; element++){
        	if(AND_needs_data[the_and][stream][element]==false){
            	proba_data_read[the_and][stream][element] = probaPrecendentLeavesTrue;
        	AND_needs_data[the_and][stream][element] = true;
        	}
        }
        probaPrecendentLeavesTrue *= DNFTree[the_and][the_leaf].proba;
        // We add the cost of the target leaf to the global cost computed so far
        Global_cost += Leaf_cost;
    }

    return (Global_cost);
}

//
// The optimal greedy algorithm to schedule the leaves of a single AND
//
void
opt_single_and(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
           long double * streamCost, int & leaf_rest, long double & bestcost,
           std::vector<multiset<Feuille> > & disjoint_set,
           vector<leaf_place> & final_order)
{
    long double proba_tot;
    long double cost;
    long double ratio;
    long double min = DBL_MAX;
    int stream_min = 0;
    int recup_min = 1;
    long double proba_min;
    int recup;
    long double cost_min = 0;
    
    
    if (leaf_rest == 0)
    {
        if (DEBUG1)
        {
            cout << "End of recursive calls to opt_single_and, bestcost : " << bestcost << endl;
            vector<leaf_place>::iterator it0;
            for (it0 = final_order.begin(); it0 < final_order.end(); it0++)
            {
                cout << " and :" << it0->get<0> () << " leaf_place :"
                << it0->get<1> () << endl;
            }
            
        }
    }
    
    else
    {
        vector<leaf_place> optimal_order;
        vector<leaf_place> evaluation_order;
        multiset<Feuille>::iterator it;
        vector<leaf_place> order_prec;
        if (DEBUG1 == 1)
        {
            cout << "**********Start of opt_single_and :" << endl;
        }
        // Loop on all the data stream
        for (int s = 0; s < nb_streams; s++)
        {
            cost = 0;
            proba_tot = 1;
            recup = 0;
            
            order_prec = final_order;
            
            // For the considered data stream, loop on all the sequences of leaves
            // made of the k leaves using the least number of elements from the considered stream
            // (but using at least one element from that stream)
            for (it = (disjoint_set[s]).begin(); it != (disjoint_set[s]).end(); it++)
            {
                if (DEBUG1)
                {
                    cout << "feuille : " << it->get<3> () << "," << it->get<4> () << ": "
                    		<< it->get<0> () << "," << it->get<1> ()
                    << endl;
                }
                evaluation_order.push_back(leaf_place(it->get<3> (), it->get<4> ()));
                order_prec.push_back(leaf_place(it->get<3> (), it->get<4> ()));
                // Evaluating the cost of the considered leaf sequence
                cost = Cost(DNFTree, nb_ands, nb_leaves_per_and, streamCost, order_prec) - bestcost;
                if (DEBUG1)
                {
                    cout << "bestcost :" << bestcost << endl;
                    cout << "cost :" << Cost(DNFTree, nb_ands, nb_leaves_per_and,
                                             streamCost, order_prec) << " -  " << bestcost << " = "
                    << cost << endl;
                }
                
                proba_tot *= it->get<2> ();

                // Computing the ratio of each sequence of leaves
                ratio = cost / (1 - proba_tot);
                if (DEBUG1)
                {
                    cout << "Ratio :" << ratio << endl;
                }
                // Keeping the best solution found so far
                if ( (ratio < min)  || (ratio <= min &&  ( evaluation_order.size() > optimal_order.size() )) )
                {
                    min = ratio;
                    cost_min = cost;
                    proba_min = proba_tot;
                    stream_min = s;
                    recup_min = it->get<0> ();
                    optimal_order = evaluation_order;
                }
                
            }
            
            evaluation_order = std::vector<leaf_place>();
        }
        
        if(min==DBL_MAX){
        	cout << "In an inifinite loop." << endl;
        	abort();
        }

        // Copy the order extension at the end of the original order
        vector<leaf_place>::iterator it2;
        for (it2 = optimal_order.begin(); it2 != optimal_order.end(); it2++)
        {
            final_order.push_back(leaf_place(it2->get<0> (), it2->get<1> ()));
            leaf_rest--;
        }
        bestcost += cost_min;
        if (DEBUG1)
        {
            cout << " ratio_min: " << min << endl;
            cout << " bestcost: " << bestcost << endl;
            cout << " recup_min: " << recup_min << endl;
            vector<leaf_place>::iterator it3;
            for (it3 = final_order.begin(); it3 < final_order.end(); it3++)
            {
                cout << " and :" << it3->get<0> () << " leaf_place :"
                << it3->get<1> () << endl;
            }
        }


        // The leaves that were added to the order are removed from the set of leaves
        for (vector<leaf_place>::iterator leaf_it = optimal_order.begin(); leaf_it != optimal_order.end(); leaf_it++){
        	int and_id = leaf_it->get<0>();
        	int leaf_id = leaf_it->get<1>();
        	multiset<Feuille>::iterator leaf_it_in_set;
        	leaf_it_in_set = (disjoint_set[stream_min]).begin();
        	bool leaf_not_found = true;
        	while(leaf_not_found &&(leaf_it_in_set!= (disjoint_set[stream_min]).end())){
        		if ((leaf_it_in_set->get<3> ()==and_id) && (leaf_it_in_set->get<4> ()==leaf_id))
        		{
        			multiset<Feuille>::iterator copy_it = leaf_it_in_set;
        			leaf_it_in_set++;
        			(disjoint_set[stream_min]).erase(copy_it);
        			leaf_not_found=false;
        		}
        		else{
        			leaf_it_in_set++;
        		}
        	}
        }


        opt_single_and(DNFTree, nb_streams, nb_ands, nb_leaves_per_and, streamCost,
                   leaf_rest, bestcost, disjoint_set, final_order);
    }
}



void
argument_processing_for_DNF(int argc, char ** argv)
{
    if (DEBUG)
    {
        cout << "Start of de lancement des heuristiques " << endl;
    }
    
    // Reading the program parameters
    // average number of leaves using data from the same stream
    double reuse = boost::lexical_cast<double>(argv[3]);

    int seed = boost::lexical_cast<int>(argv[5]);

    int nb_streams  = boost::lexical_cast<int>(argv[7]);


    // Number of ANDs
    int nb_ands = boost::lexical_cast<int>(argv[9]);
    // Maximum number of leaves of an AND
    int nbmaxleaves = boost::lexical_cast<int>(argv[11]);
    
    // Number of leaves per AND
    int * nb_leaves_per_and = new int[nb_ands];
    for (int j = 0; j < nb_ands; j++)
    {
        nb_leaves_per_and[j] = boost::lexical_cast<int>(argv[13 + j]);
    }
    
    // Allocating the DNF data structure that holds the description of the DNF tree
    // and storing in it the input DNF
    int k = 1;
    leaf ** DNF = new leaf *[nb_ands];
    for (int j = 0; j < nb_ands; j++)
    {
        DNF[j] = new leaf[nb_leaves_per_and[j]];
        for (int i = 0; i < nb_leaves_per_and[j]; i++)
        {
            DNF[j][i].stream = boost::lexical_cast<int>(argv[9+ 3 + nb_ands + 1 + k]);
            DNF[j][i].nb_data_recup = boost::lexical_cast<int>(
                                                               argv[9+ 3 + nb_ands + 1 + (k + 1)]);
            DNF[j][i].proba = boost::lexical_cast<long double>(
                                                               argv[9+ 3 + nb_ands + 1 + (k + 2)]);
            DNF[j][i].full_eval = 0;
            DNF[j][i].eval_order = 0;
            k = k + 3;
        }
    }
    

    if (DEBUG)
    {
        cout << "nb_streams =" << nb_streams << endl;
    }
    // Reading the cost of the different streams
    long double * streamCost = new long double[nb_streams];
    for (int s = 0; s < nb_streams; s++)
    {
        streamCost[s] = boost::lexical_cast<long double>(argv[9+ 3 + nb_ands + 1 + k + 1 + s]);
    }

    int heuristic_code = boost::lexical_cast<int>(argv[9+ 3 + nb_ands + 1 + k + nb_streams+2]);
    bool with_optimal = false;
    bool with_optimal_singlestream = false;
    bool with_progdyn = false;
    bool with_heuristics = false;
	bool with_single_and = false;
	bool with_lipyeow = true;
	bool only_best_one = false;
    switch(heuristic_code){
    case 0:
    	with_optimal = true;
    	with_optimal_singlestream = false;
    	with_progdyn = false;
    	with_heuristics = true;
    	with_single_and = false;
    	break;
    case 1:
    	with_optimal = false;
    	with_optimal_singlestream = false;
    	with_progdyn = false;
    	with_heuristics = true;
    	with_single_and = false;
    	break;
    case 2:
    	with_optimal = false;
    	with_optimal_singlestream = false;
    	with_progdyn = false;
    	with_heuristics = true;
    	with_single_and = false;
    	break;
    case 3:
    	with_optimal = false;
    	with_optimal_singlestream = false;
    	with_progdyn = false;
    	with_heuristics = false;
    	with_single_and = true;
    	break;
    case -1:
    	with_optimal = true;
    	with_optimal_singlestream = true;
    	with_progdyn = false;
    	with_heuristics = false;
    	with_single_and = false;
    	break;
    case -2:
    	with_optimal = false;
    	with_optimal_singlestream = true;
    	with_progdyn = false;
    	with_heuristics = false;
    	with_single_and = false;
    	break;
    case -10:
    	with_optimal = false;
    	with_optimal_singlestream = false;
    	with_progdyn = false;
    	with_heuristics = false;
    	with_single_and = false;
    	only_best_one = true;
    	break;
    default:
    	cerr << "ERROR: heuristic code " << heuristic_code << " is unknown." << endl;
    	abort();
    }
    
    int Sum_max_recup = 0;
    unsigned long int nb_cases = 1;
    unsigned long int previous_nb_cases = 0;
    int int_overflow_for_progdyn = 0;

    // Computing the maximum number of elements retrieved from each stream
    std::vector<int> vector_max(nb_streams, 0);
    for (int s = 0; s < nb_streams; s++)
    {
        vector_max[s] = 0;
        for (int j = 0; j < nb_ands; j++)
        {
            for (int i = 0; i < nb_leaves_per_and[j]; i++)
            {
                if ((DNF[j][i].stream == s) && (vector_max[s]
                                                < DNF[j][i].nb_data_recup))
                {
                    vector_max[s] = DNF[j][i].nb_data_recup;
                }
            }
        }
        
        Sum_max_recup += vector_max[s];
        if (DEBUG)
        {
            cout << "Sum_max_recup =" << Sum_max_recup << endl;
        }
        previous_nb_cases = nb_cases;
        nb_cases *= (vector_max[s] + 1);
        if(nb_cases < previous_nb_cases){
        	int_overflow_for_progdyn = 1;
        	if (DEBUG) cout << "Integer overflow..." << endl;
        }
        if (DEBUG)
        cout << "nb_cases for " << s << " = " << nb_cases << endl;
        
    }
    if (int_overflow_for_progdyn) nb_cases = 1;
    
    
   if (DEBUG)
    {
        cout << "vector_max: ";
        for (int i = 0; i < nb_streams; i++)
        {
            cout << vector_max[i] << " ,";
        }
        cout << "nb_cases =" << nb_cases << endl;
    }
    
    std::vector<int> vector_init(nb_streams, 0);
    
    case_elem init;
    init.vu = false;
    init.cost = 0;
    init.next_stream = -1;
    init.vector_value = vector_init;
    


    
    
    // Computing the proba of successfull evaluation of each AND
    std::vector<long double> proba_and(nb_ands, 1);
    for (int j = 0; j < nb_ands; j++)
    {
        for (int i = 0; i < nb_leaves_per_and[j]; i++)
        {
            proba_and[j] *= DNF[j][i].proba;
        }
    }
    
    if (DEBUG)
    {
        cout << "proba_and: ";
        for (int i = 0; i < nb_ands; i++)
        {
            cout << proba_and[i] << " ,";
        }
        cout << endl;
    }

    // Opening the output file
    ofstream outputfile;
    char * filename = new char [2048];
    sprintf(filename, "DNFTREE-%s-%d-%d-%.2f", argv[1], nb_ands, nbmaxleaves, reuse);
    outputfile.open(filename, ios::app);
    if (!(outputfile.is_open()))
    {
    	cout << "ERROR opening file: " << filename << endl;
    	abort();
    }
    // Copy the arguments of the program call
    outputfile << "# ARGUMENTS\t";
    for(int i=1; i<argc; i++){
    	outputfile << argv[i] << " ";
    }
    outputfile << endl;;

    long double cost_optimal = DBL_MAX;
    long double cost_optimal_singlestream = DBL_MAX;
    long double costeval_andbyand_byc_over_p = DBL_MAX;
    long double costeval_andbyand_bycost = DBL_MAX;
    long double costorderleaves_byc_over_q = DBL_MAX;
    long double costorderleaves_byc_over_p = DBL_MAX;
    long double costorderleaves_bycost = DBL_MAX;
    long double costorderleaves_bydecreasingproba = DBL_MAX;
    long double costorderleaves_byincreasingproba = DBL_MAX;
    long double costorder_andbyand_static_by_c_over_p = DBL_MAX;
    long double costorder_andbyand_static_by_cost = DBL_MAX;
    long double costorder_andbyand_static_by_increasingproba = DBL_MAX;
    long double costorder_andbyand_static_by_decreasingproba = DBL_MAX;

    if(with_optimal){
    	//*********************** Calling the exhaustive search for the optimal
    	exhaustive_andbyand(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams,
    	                      cost_optimal);
    	outputfile << seed << "\t"  << "0\t" << cost_optimal << endl;
    }
    if(with_optimal_singlestream){
    	//*********************** Calling the exhaustive search for the optimal
    	exhaustive_andbyand_singlestream(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams,
    			cost_optimal_singlestream);
    	outputfile << seed << "\t"  << "1\t" << cost_optimal_singlestream << endl;
    	if ((with_optimal)&&((cost_optimal-cost_optimal_singlestream > 0.00001)||(cost_optimal_singlestream-cost_optimal > 0.00001))){
    		outputfile << "Big difference " << endl;
    		abort();
    	}
    }



    if(with_heuristics||with_single_and||only_best_one){
        //*********************** Calling heuristic  eval_andbyand_byc_over_p:heur1
        costeval_andbyand_byc_over_p = 0;

        eval_andbyand_dynamic_by_c_over_p(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams, costeval_andbyand_byc_over_p);

    	outputfile << seed << "\t"  << "20\t" << costeval_andbyand_byc_over_p << endl;
    }



    if(with_heuristics){
        //*********************** Calling heuristic  eval_andbyand_bycost:heur2
        costeval_andbyand_bycost = 0;

        eval_andbyand_dynamic_bycost(DNF, nb_ands,
                             nb_leaves_per_and, streamCost, proba_and, nb_streams, costeval_andbyand_bycost);
    	outputfile << seed << "\t"  << "21\t" << costeval_andbyand_bycost << endl;
    }

    if(with_heuristics || with_single_and){
        //*********************** Calling heuristic orderleaves_byc_over_q:heur4
        vector<leaf_place> evaluation_order4;
        costorderleaves_byc_over_q = orderleaves_by_c_over_q(DNF, nb_ands,
                                                    nb_leaves_per_and, streamCost, evaluation_order4);
    	outputfile << seed << "\t"  << "40\t" << costorderleaves_byc_over_q << endl;
    }
    if(with_heuristics){
        //*********************** Calling heuristic orderleaves_byc_over_p:heur5
        vector<leaf_place> evaluation_order5;
        costorderleaves_byc_over_p = orderleaves_by_c_over_p(DNF, nb_ands,
                                                    nb_leaves_per_and, streamCost, evaluation_order5);
    	outputfile << seed << "\t"  << "41\t" << costorderleaves_byc_over_p << endl;

        //*********************** Calling heuristic orderleaves_bycost:heur6
        vector<leaf_place> evaluation_order6;
        costorderleaves_bycost = orderleaves_bycost(DNF, nb_ands,
                                                  nb_leaves_per_and, streamCost, evaluation_order6);
    	outputfile << seed << "\t"  << "42\t" << costorderleaves_bycost << endl;

        
        //*********************** Calling heuristic orderleaves_bydecreasingproba:heur7
        vector<leaf_place> evaluation_order7;
        costorderleaves_bydecreasingproba = orderleaves_bydecreasingproba(DNF, nb_ands,
                                                                        nb_leaves_per_and, streamCost, evaluation_order7);
    	outputfile << seed << "\t"  << "43\t" << costorderleaves_bydecreasingproba << endl;

        //*********************** Calling heuristic orderleaves_byincreasingproba:heur8
        vector<leaf_place> evaluation_order8;
        costorderleaves_byincreasingproba = orderleaves_byincreasingproba(DNF, nb_ands,
                                                                        nb_leaves_per_and, streamCost, evaluation_order8);
    	outputfile << seed << "\t"  << "44\t" << costorderleaves_byincreasingproba << endl;

        // Calling heuristic order_leaves_randomly
    	long double cost_random_ordering = order_leaves_randomly(DNF, nb_ands, nb_leaves_per_and, streamCost);
    	outputfile << seed << "\t"  << "45\t" << cost_random_ordering << endl;

    	if(with_lipyeow){
    		// Calling the heuristic taken from the paper by Lipyeow
    		long double cost_by_lipyeow_decreasing = Lipyeow_ordering(DNF, nb_ands, nb_leaves_per_and, streamCost, nb_streams, true);
    		outputfile << seed << "\t"  << "46\t" << cost_by_lipyeow_decreasing << endl;
    		long double cost_by_lipyeow_increasing = Lipyeow_ordering(DNF, nb_ands, nb_leaves_per_and, streamCost, nb_streams, false);
    		outputfile << seed << "\t"  << "47\t" << cost_by_lipyeow_increasing << endl;
    	}
        //*********************** Calling heuristic order_andbyand_static_by_c_over_p:heur9
        costorder_andbyand_static_by_c_over_p = 0;

        order_andbyand_static_by_c_over_p(DNF, nb_ands,
                          nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andbyand_static_by_c_over_p
                          );
    	outputfile << seed << "\t"  << "30\t" << costorder_andbyand_static_by_c_over_p << endl;

        //*********************** Calling heuristic order_andbyand_static_by_cost:heur10
        costorder_andbyand_static_by_cost = 0;
        

        order_andbyand_static_by_cost(DNF, nb_ands,
                         nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andbyand_static_by_cost
                         );
    	outputfile << seed << "\t"  << "31\t" << costorder_andbyand_static_by_cost << endl;

        //*********************** Calling heuristic order_andbyand_static_by_increasingproba:heur11
        costorder_andbyand_static_by_increasingproba = 0;

        order_andbyand_static_by_increasingproba(DNF, nb_ands,
                                    nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andbyand_static_by_increasingproba
                                    );
    	outputfile << seed << "\t"  << "32\t" << costorder_andbyand_static_by_increasingproba << endl;

        //*********************** Calling heuristic order_andbyand_static_by_decreasingproba:heur12
        costorder_andbyand_static_by_decreasingproba = 0;
        
        order_andbyand_static_by_decreasingproba(DNF, nb_ands,
                                    nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andbyand_static_by_decreasingproba
                                    );
    	outputfile << seed << "\t"  << "33\t" << costorder_andbyand_static_by_decreasingproba << endl;

    }

    long double cost_progdyn = 0;
    if(with_progdyn){
        //*********************** Calling heuristic prog_dyn:heur0
        if(int_overflow_for_progdyn){
        	outputfile << "#INT OVERFLOW  for progdyn" << endl;
        }
        else{
        	long double progdyn = -1;
        	std::vector<int> best_stream_order;

        	int data_element_size = sizeof(bool) + sizeof(long double) + sizeof(int) + nb_streams*sizeof(int);
        	if (MYDEBUG) cout << "Memory allocation of " << nb_cases << " elements of size " << data_element_size << endl;
        	if (MYDEBUG) cout << "Equivalent to " << nb_cases*1.0*data_element_size/1073741824.0 << " GB" << endl;
        	std::vector<case_elem> marqueurs(nb_cases, init);

        	// Call to the function doing the work
        	if (MYDEBUG) cout << "CALL to the dynamic programming algorithm." << endl;
        	progdyn = prog_dyn_DNF(0, DNF, nb_streams, streamCost, nb_ands, nb_leaves_per_and,
        			marqueurs, vector_max, nb_cases, best_stream_order);
        	if (MYDEBUG) cout << "AFTER the call to the dynamic programming algorithm." << endl;
        	if(DEBUG2){
        		cout << endl << "#####################Cost_progdyn :#################### "
        				<< progdyn << endl;
        		//Affichage de la solution optimale
        		vector<int>::iterator it;
        		cout << "##################### La solution optimale de progdyn est : {";
        		for (it = best_stream_order.begin(); it < best_stream_order.end(); it++)
        		{
        			cout << *it << ", ";

        		}
        		cout << "} " << endl;
        	}

        	std::vector<int> compteur(nb_streams, 0);
        	vector<leaf_place> evaluation_order0;
        	// Call to the function doing the work
        	cost_progdyn = Costprog_dyn_DNF(DNF, nb_streams, streamCost, nb_ands,
        			nb_leaves_per_and, compteur, best_stream_order, evaluation_order0);

        	outputfile << seed << "\t"  << "10\t" << cost_progdyn << endl;
        }
    }//fin if progdyn

    
    for (int j = 0; j < nb_ands; j++){
    	delete [] DNF[j];
    }
    delete [] DNF;
    delete [] streamCost;
    delete [] nb_leaves_per_and;
}

int
main(int argc, char ** argv)
{
    argument_processing_for_DNF(argc, argv);
}

