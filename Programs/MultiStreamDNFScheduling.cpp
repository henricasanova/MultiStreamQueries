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
#include "MultiStream.hpp"
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
					for(int k=0; k<nb_streams; k++){
						// If there were so far fewer elements retrieved from one stream the leaf depends upon than what the leaf needs
						// then neither the leaf not its AND are completed, and the AND needs data from that stream
						if (marqueurs[cas].vector_value[k] < DNF[j][i].nb_data_recup[k]){
							andCompleted[j] = false;
							leafCompleted[j][i] = false;
							andNeedStream[j][k] = true;
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
	long double meilleurcost;

	// Initialization of the data structure used to record from how many of the data streams a leaf depends upon
	// were enough data retrieved to enable the evaluation of the leaf
	for (int j = 0; j < nb_ands; j++){
		for (int i = 0; i < nb_leaves_per_and[j]; i++){
			DNF[j][i].full_eval = 0;
			for(int k=0; k<nb_streams; k++){
				if (DNF[j][i].nb_data_recup[k]==0){
					DNF[j][i].full_eval++;
				}
			}
		}
	}

	// Build a leaf order from a data retrieval order
	// Traversal of the data retrieval order
	for (std::vector<int>::iterator it = best_stream_order.begin(); it < best_stream_order.end(); it++){
		compteur[(*it)]++;
		// Loop on all the leaves
		for (int j = 0; j < nb_ands; j++){
			for (int i = 0; i < nb_leaves_per_and[j]; i++){
				for (int k=0; k< nb_streams; k++){
					// If test is true, then a new stream for that leaf is just completed at that stage
					if (DNF[j][i].nb_data_recup[(*it)] == compteur[(*it)]){
						DNF[j][i].full_eval ++;
						// If, after that read, the whole leaf has all its necessary input data
						if(DNF[j][i].full_eval==nb_streams){
							long double proba = DNF[j][i].proba;
							leaves_order.insert(ratio_leaf(proba, j, i));
						}
					}
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
	long double optimized_cost = Cost4Arrays(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost,
			nb_leaves, order_and_id, order_leaf_id);
	//Deallocation
	delete [] order_and_id;
	delete [] order_leaf_id;

	meilleurcost = Cost(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order);
	if(optimized_cost > meilleurcost){
		cout << "meilleur cost = " << meilleurcost << " < " << optimized_cost << "optimized_cost" << endl;
	}
	assert(meilleurcost >= optimized_cost);
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
    vector<leaf_place> optimal_leaf_order;
    vector<leaf_place> final_order;

    vector<leaf_place> optimal_order;
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
            final_order = evaluation_order;

            cost = prec_bestcost;
            // Call to the greedy algorithm that optimally schedules the leaves of a single AND
            MultiStreamGreedy(DNF, nb_streams, nb_ands, nb_leaves_per_and, streamCost, *it, cost, final_order);

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
        bestcost = Cost(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order);
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
                   int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order, long double heur)
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
        	cost = 0;
        	for(int stream_id=0; stream_id<nb_streams; stream_id++){
        		cost += DNF[j][i].nb_data_recup[stream_id]*streamCost[stream_id];
        	}

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
    bestcost = Cost(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order);
    if(DEBUG2){
        cout << "# bestcost : "<< bestcost << endl;
    }
    return (bestcost);
}



//
// Heuristic ordering leaves by the ratio: cost / (1-proba)
//
long double
orderleaves_by_c_over_q(leaf ** DNF, int nb_ands, int * nb_leaves_per_and, int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_by_c_over_q :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order, 4);
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
		int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_byc_over_p :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order, 5);
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
		int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_bycost :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order, 6);
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
		int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_bydecreasingproba :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order, 7);
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
		int nb_streams, long double * streamCost, vector<leaf_place> & evaluation_order)
{
    long double bestcost = 0;
    if(DEBUG2){
        cout << " ***** Start of heuristic orderleaves_byincreasingproba :" << endl;
    }
    bestcost= orderleaves_byratio(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order, 8);
    if(DEBUG2){cout << " ***** End of heuristic orderleaves_byincreasingproba****" << endl;
    }
    return (bestcost);
}
//
// Random ordering of the leaves
//
long double order_leaves_randomly(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
		int nb_streams, long double * streamCost){
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
		leaf_order.push_back(leaf_place(global2local_and[random_leaf_order[leaf_id]], global2local_leaf[random_leaf_order[leaf_id]]));
	}
	long double cost = Cost(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, leaf_order);

	delete [] global2local_leaf;
	delete [] global2local_and;
	delete [] random_leaf_order;

	return cost;
}



//****************************************l'heuristique general order_andby_ratio****************************************
void
order_andby_ratio(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                  long double * streamCost, vector<long double> proba_and, int nb_streams,
                  long double & meilleurcost, multiset<int> and_rest,
                  multiset<ratio_and> and_final_order,
                  vector<vector<leaf_place> > leaf_order,
                  std::vector<multiset<Feuille> > & disjoint_set,
                  vector<leaf_place> evaluation_order, int heur)
{
    vector<leaf_place> final_order;

    vector<leaf_place> optimal_order;
    //vector< leaf_place>  order_prec;
    long double bestcost;
    multiset<int>::iterator it;

    long double ratio = 1;

    //cout << "********************Debut heuiristique order_andby_ratio*********************** ";
    if( DEBUG2 ) {
        multiset<int>::iterator it0;
        for (it0 = and_rest.begin(); it0 != and_rest.end(); it0++)
        {

            cout << *it0 << " , ";
        }
        cout << endl;
    }
    for (it = and_rest.begin(); it != and_rest.end(); it++)
    {
        //cout << "&&&&&&&&& Debut and :" << *it << endl;
        final_order = evaluation_order;
        bestcost = 0;

        MultiStreamGreedy(DNF, nb_streams, nb_ands, nb_leaves_per_and, streamCost, *it, bestcost, final_order);

        if(heur==9){
            ratio = bestcost / proba_and[*it];
        }
        if(heur==10){
            ratio = bestcost;
        }
        if(heur==11){
            ratio = proba_and[*it];
        }

        if(heur==12){
            ratio = 1 / proba_and[*it];
        }

        if (DEBUG1)
        {
            cout << "bestcost : " << bestcost << " ,andj : " << *it << endl;
            cout << "Ratio :" << ratio << endl;
        }
        and_final_order.insert(ratio_and(ratio, *it));
        leaf_order[*it] = final_order;
    }

    multiset<ratio_and>::iterator it2;
    vector<leaf_place>::iterator it4;

    for (it2 = and_final_order.begin(); it2 != and_final_order.end(); it2++)
    {
        int andj = it2->get<1> ();
        for (it4 = leaf_order[andj].begin(); it4 != leaf_order[andj].end(); it4++)
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
    meilleurcost = Cost(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost, evaluation_order);
    if(DEBUG2){
        cout
        << "##Meilleurcost : "<< meilleurcost << endl;

    }
}

//****************************************heuristique 9 est l'heuristique  order_andby_csurp****************************************
void
order_andby_csurp(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                  long double * streamCost, vector<long double> proba_and, int nb_streams,
                  long double & meilleurcost, multiset<int> and_rest,
                  multiset<ratio_and> and_final_order,
                  vector<vector<leaf_place> > leaf_order,
                  std::vector<multiset<Feuille> > & disjoint_set,
                  vector<leaf_place> evaluation_order){
    if(DEBUG2){
        cout
        << "********************Debut heuiristique order_andby_csurp*********************** "<< endl;
    }
    order_andby_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, meilleurcost, and_rest,
                      and_final_order,leaf_order,disjoint_set,evaluation_order, 9);

    if(DEBUG2){
        cout
        << "********************Fin heuiristique order_andby_csurp*********************** "<< endl;
    }
}
//****************************************heuristique 10 est l'heuristique order_andby_cost****************************************
void
order_andby_cost(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                 long double * streamCost, vector<long double> proba_and, int nb_streams,
                 long double & meilleurcost, multiset<int> and_rest,
                 multiset<ratio_and> and_final_order,
                 vector<vector<leaf_place> > leaf_order,
                 std::vector<multiset<Feuille> > & disjoint_set,
                 vector<leaf_place> evaluation_order)
{if(DEBUG2){
    cout
    << "********************Debut heuiristique order_andby_cost*********************** "<< endl;
}
    order_andby_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, meilleurcost, and_rest, and_final_order,
                      leaf_order,disjoint_set,evaluation_order, 10);

    if(DEBUG2){
        cout
        << "********************Fin heuristique order_andby_cost*********************** "<< endl;
    }
}
//****************************************heuristique 11 est l'heuristique order_andby_increasingproba****************************************
void
order_andby_increasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                            long double * streamCost, vector<long double> proba_and, int nb_streams,
                            long double & meilleurcost, multiset<int> and_rest,
                            multiset<ratio_and> and_final_order,
                            vector<vector<leaf_place> > leaf_order,
                            std::vector<multiset<Feuille> > & disjoint_set,
                            vector<leaf_place> evaluation_order)
{
    if(DEBUG2){
        cout
        << "********************Debut heuiristique order_andby_increasingproba*********************** "<< endl;

    }
    order_andby_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, meilleurcost, and_rest, and_final_order,
                      leaf_order,disjoint_set,evaluation_order, 11);

    if(DEBUG2){
        cout
        << "********************Fin heuiristique order_andby_increasingproba*********************** "<< endl;
    }
}
//****************************************heuristique 12 est l'heuristique order_andby_decreasingproba****************************************
void
order_andby_decreasingproba(leaf ** DNF, int nb_ands, int * nb_leaves_per_and,
                            long double * streamCost, vector<long double> proba_and, int nb_streams,
                            long double & meilleurcost, multiset<int> and_rest,
                            multiset<ratio_and> and_final_order,
                            vector<vector<leaf_place> > leaf_order,
                            std::vector<multiset<Feuille> > & disjoint_set,
                            vector<leaf_place> evaluation_order)
{
    if(DEBUG2){
        cout
        << "********************Debut heuiristique order_andby_decreasingproba*********************** "<< endl;
    }
    order_andby_ratio(DNF, nb_ands,  nb_leaves_per_and, streamCost, proba_and, nb_streams, meilleurcost, and_rest, and_final_order,
                      leaf_order,disjoint_set,evaluation_order, 12);

    if(DEBUG2){
        cout
        << "********************Fin heuiristique order_andby_decreasingproba*********************** "<< endl;
    }
}
//********************************************************************************
long double
Cost(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, int nb_streams, long double * streamCost,
     vector<leaf_place> evaluation_order)
{
    
    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
//    int nb_data_recup;
//    int stream;
//    long double proba;
    int And_eval;
    vector<leaf_place>::iterator it;
    
    bool * andCompleted = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        andCompleted[k] = false;
    }
    
    bool * Needingand = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        Needingand[k] = false;
    }
    
    int Need_stream = 0;
    int * minleaf = new int[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        minleaf[k] = -1;
    }
    
    long double * probaAndTrue = new long double[nb_ands];
    long double probaPrecendentLeafTrue = 1;
    
    //Mise  O de tous les full_eval des feuilles de l'arbre
    for (int k = 0; k < nb_ands; k++)
    {
        for (int i = 0; i < nb_leaves_per_and[k]; i++)
        {
            DNFTree[k][i].full_eval = 0;
        }
    }
    
    //Mise  jour des ordres d'evaluation des feuilles selon la stratgie
    int ind = -1;
    for (it = evaluation_order.begin(); it < evaluation_order.end(); it++)
    {
        ind++;
 //       cout << it->get<0> () << "\t" << it->get<1> () << endl; //FORDEBUG
        DNFTree[it->get<0> ()][it->get<1> ()].eval_order = ind;
    }
    
    //Calcul du cout global de la strategie
    for (it = evaluation_order.begin(); it < evaluation_order.end(); it++) //une boucle qui prend feuille par feuille dans l'ordre d'evaluation
    {
        //initialisation des variables pour chaque feuille
        Leaf_cost = 0;
        if (DEBUG == 1)
        {
            cout << "Feuille with and :" << it->get<0> () << "  and leaf_place :"
            << it->get<1> () << endl;
        }
        
        
        //Calcul de la probabilite du succes des feuilles qui precede la feuille tudie dans son AND
        probaPrecendentLeafTrue = 1;
        for (int i = 0; i < nb_leaves_per_and[it->get<0> ()]; i++)
        {
            if (DNFTree[it->get<0> ()][i].full_eval == 1)
            {
                probaPrecendentLeafTrue = probaPrecendentLeafTrue
                * DNFTree[it->get<0> ()][i].proba;
            }
        }
        if (DEBUG == 1)
        {
            cout << "probaPrecendentLeafTrue : " << probaPrecendentLeafTrue
            << endl;
        }
        
        //long double proba = DNFTree[it->get<0> ()][it->get<1> ()].proba;
        for(int stream=0; stream< nb_streams; stream++){
        	int nb_data_recup = DNFTree[it->get<0> ()][it->get<1> ()].nb_data_recup[stream];
        	//stream = DNFTree[it->get<0> ()][it->get<1> ()].stream;

        int nb_recup = 0;
        for (int e = 0; e < nb_data_recup; e++)//une boucle sur les elements de la feuille tudie
        {
            nb_recup++;
            for (int k = 0; k < nb_ands; k++)
            {
                andCompleted[k] = false;
                Needingand[k] = false;
                probaAndTrue[k] = 1;
            }
            
            int trouve = 0;
//            multiset<Feuille> list_leafs;
            for (int j = 0; j < nb_ands; j++)
            {
                And_eval = 0;
                Need_stream = 0;
                int eval_rank = INT_MAX;
                for (int i = 0; i < nb_leaves_per_and[j]; i++)
                {
                    //cout<<"****stream :"<<stream<<" ,DNFTree["<<j<<"]["<<i<<"] .full_eval :"<<DNFTree[j][i].full_eval<<", DNFTree["<<j<<"]["<<i<<"].stream :"<<DNFTree[j][i].stream
                    //  <<", DNFTree["<<j<<"]["<<i<<"].nb_data_recup :"<<DNFTree[j][i].nb_data_recup<<endl;
                    if (DNFTree[j][i].full_eval == 1)
                    {
                        And_eval++;
                        //if(trouve==0){
                        if (DNFTree[j][i].nb_data_recup[stream] >= nb_recup)
                        {
                            Need_stream = 1;
                            Needingand[j] = true;
                            
                            if(DNFTree[j][i].eval_order < eval_rank){
                            	eval_rank = DNFTree[j][i].eval_order;
                            	minleaf[j] = i;
                            }

//                            list_leafs.insert(
//                                              Feuille(DNFTree[j][i].nb_data_recup,
//                                                      DNFTree[j][i].stream, DNFTree[j][i].proba, j,
//                                                      i));
//
                            trouve = 1;
                        }
                        //}//if trouve
                        
                    }
                    probaAndTrue[j] = probaAndTrue[j] * DNFTree[j][i].proba;
                }
                
//                multiset<Feuille>::iterator it;
//                it = list_leafs.begin();
//                minleaf[j] = it->get<4> ();
//                list_leafs.clear();
                
                if ((And_eval == nb_leaves_per_and[j]) && Need_stream == 0)
                    andCompleted[j] = true;
                //cout<<" probaAndTrue[" <<j<<"] : "<<probaAndTrue[j]<<endl;
                //cout<<"trouve :"<<trouve<<endl;
            }
            
            //Calcul de la probabilite du succes des feuilles qui precede la minleaf dans son AND,
            //la minleaf c'est la feuille qui peut charger la stream et qui a un nb_data_recup>=nb_recup
            long double * probaPrecendentNeedleaf = new long double[nb_ands];
            for (int k = 0; k < nb_ands; k++)
            {
                probaPrecendentNeedleaf[k] = 1;
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
                            
                            probaPrecendentNeedleaf[j]
                            = probaPrecendentNeedleaf[j]
                            * DNFTree[j][i].proba;
                        }
                    }//for i
                }
                if (DEBUG == 1)
                {
                    cout << "probaPrecendentNeedleaf[" << j << "] : "
                    << probaPrecendentNeedleaf[j] << endl;
                }
            }//for j
            
            
            long double probaCompletedAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
                if (andCompleted[j] == true)
                {
                    probaCompletedAndsFalse = probaCompletedAndsFalse * (1
                                                                         - probaAndTrue[j]);
                    //cout<<" probaCompletedAndsFalse :"<<probaCompletedAndsFalse<<endl;
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
                    probaNeedingAndsFalse = probaNeedingAndsFalse * (1
                                                                     - probaPrecendentNeedleaf[j]);
                }
            }
            if (DEBUG == 1)
            {
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }
            delete [] probaPrecendentNeedleaf;
            
            //Le cas si l'element e est un nouveau element  charger (trouve =0 veut dire on n'a pas trouv que e peut tre charg quelque part)
            if (trouve == 0)
            {
                Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeafTrue
                * streamCost[stream];
                if (DEBUG == 1)
                {
                    cout << "trouve :" << trouve << " ,probaPrecendentLeafTrue :"
                    << probaPrecendentLeafTrue << " ,leafcost :"
                    << probaCompletedAndsFalse * probaPrecendentLeafTrue
                    * streamCost[stream] << "nb_recup :" << nb_recup
                    << endl;
                }
            }
            
            else
            {
                
                //Le cas o l'element e peut tre charger par le AND de la feuille tudie
                if (Needingand[it->get<0> ()] == true)
                {
                    Leaf_cost += 0;
                    if (DEBUG == 1)
                    {
                        cout << "trouve :" << trouve << " ,leafcost :" << 0
                        << "nb_recup :" << nb_recup << endl;
                    }
                }
                //Le cas o l'element e peut tre charger par les autres NeedingAND
                else
                {
                    //Le cas o l'element e peut tre charger par les autres NeedingAND
                    Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse
                                                          * probaPrecendentLeafTrue) * streamCost[stream];
                    if (DEBUG == 1)
                    {
                        cout << "trouve :" << trouve << " ,leafcost :"
                        << probaNeedingAndsFalse * (probaCompletedAndsFalse
                                                    * probaPrecendentLeafTrue) * streamCost[stream]
                        << " ,nb_recup :" << nb_recup << endl;
                    }
                }
            }
        }
        }
        
        DNFTree[it->get<0> ()][it->get<1> ()].full_eval = 1;
        Global_cost += Leaf_cost;
        //cout<<"!!!!!!!Global_cost :"<<Global_cost<<endl;
    }
    
    delete [] probaAndTrue;
    delete [] minleaf;
    delete [] Needingand;
    delete [] andCompleted;

    return (Global_cost);
}

// Same function as above, but working on an array description of the order rather than on a vector description
long double
Cost4Arrays(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, int nb_streams, long double * streamCost,
		int nb_leaves, int * and_id, int * leaf_id)
{

//	if (DEBUG){
//		cout << endl;
//		for(int leaf_rank=0; leaf_rank<nb_leaves; leaf_rank++)
//			//    	//une boucle qui prend feuille par feuille dans l'ordre d'evaluation
//		{
//			// Retrieval of the identity and characteristics of the ``target'' leaf
//			//        //initialisation des variables pour chaque feuille
//			int the_and = and_id[leaf_rank];
//			int the_leaf = leaf_id[leaf_rank];
////			cout << the_and << "\t" << DNFTree[the_and][the_leaf].stream << "\t" << DNFTree[the_and][the_leaf].nb_data_recup << "\t" << DNFTree[the_and][the_leaf].proba << endl;
//		}
//		cout << endl;
//	}


    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
//    int nb_data_recup;
//    int stream;
//    long double proba;
    int nb_leaves_evaluated;
    //vector<leaf_place>::iterator it;

    long double * probaPrecendentNeedleaf = new long double[nb_ands];

    bool * andCompleted = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        andCompleted[k] = false;
    }

    bool * Needingand = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        Needingand[k] = false;
    }

    int Need_stream = 0;
    int * minleaf = new int[nb_ands];
    for (int k = 0; k < nb_ands; k++)
    {
        minleaf[k] = -1;
    }

    long double * probaAndTrue = new long double[nb_ands];
    long double probaPrecendentLeafTrue = 1;

    // The full_eval field of each leaf is initialized to 0
    //    //Mise  O de tous les full_eval des feuilles de l'arbre
    for (int k = 0; k < nb_ands; k++)
    {
        for (int i = 0; i < nb_leaves_per_and[k]; i++)
        {
            DNFTree[k][i].full_eval = 0;
        }
    }

    // The rank of each leaf is stored in the DNF datavstructure
    // It is computed from the evaluation order given as argument to the function
    //    //Mise  jour des ordres d'evaluation des feuilles selon la stratgie
    for(int i=0; i<nb_leaves; i++){
    	DNFTree[and_id[i]][leaf_id[i]].eval_order = i;
    }

    // Computation of the global cost
    // We compute the cost induced by each leaf, considering leaves one by one in the evaluation order
    //    //Calcul du cout global de la strategie
    for(int leaf_rank=0; leaf_rank<nb_leaves; leaf_rank++)
    	//    	//une boucle qui prend feuille par feuille dans l'ordre d'evaluation
    {
    	// Retrieval of the identity and characteristics of the ``target'' leaf
    	//        //initialisation des variables pour chaque feuille
        int the_and = and_id[leaf_rank];
        int the_leaf = leaf_id[leaf_rank];
        Leaf_cost = 0;
        for(int stream=0; stream<nb_streams; stream++){
        int nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup[stream];
        //stream = DNFTree[the_and][the_leaf].stream;
        //proba = DNFTree[the_and][the_leaf].proba;
        // Initialization of the leaf cost

        if (DEBUG == 1)
        {
            cout << "Feuille with and: " << the_and << "  and leaf_place: "
            << the_leaf << " stream " << stream << " nb_data_recup " << nb_data_recup << endl;
        }

        //        //Calcul de la probabilite du succes des feuilles qui precede la feuille tudie dans son AND
        // If the AND the target leaf belongs to is evaluated, computation of the probability that the target leaf itself is evaluated
        // This is the product of the probability of success of this AND leaves that are executed (in the order) before the target leaf
        probaPrecendentLeafTrue = 1;
        for (int i = 0; i < nb_leaves_per_and[the_and]; i++)
        {
            if (DNFTree[the_and][i].full_eval == 1)
            {
                probaPrecendentLeafTrue *= DNFTree[the_and][i].proba;
            }
        }
        if (DEBUG == 1)
        {
            cout << "probaPrecendentLeafTrue : " << probaPrecendentLeafTrue
            << endl;
        }

        // We consider one by one all the input data elements the target leaf depends upon
        int nb_recup = 0;
        for (int e = 0; e < nb_data_recup; e++)
        	//        	//une boucle sur les elements de la feuille tudie
        {
            nb_recup++;
            // Initializations...
            for (int k = 0; k < nb_ands; k++)
            {
                andCompleted[k] = false;
                Needingand[k] = false;
                probaAndTrue[k] = 1;
            }

            int trouve = 0;
//            multiset<Feuille> list_leafs;
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
                        if (DNFTree[j][i].nb_data_recup[stream] >= nb_recup)
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
//                            list_leafs.insert(
//                                              Feuille(DNFTree[j][i].nb_data_recup,
//                                                      DNFTree[j][i].stream, DNFTree[j][i].proba, j,
//                                                      i));

                            trouve = 1;
                        }
                    }
                	// Computing the overall probability of success of the evaluation of the considered AND
                    probaAndTrue[j] *= DNFTree[j][i].proba;
                }

//                // Just record (!?!) the identifier of the first leaf (in number order, not evaluation order) of the AND that requires the conidered input data element
//                // BUG
//                multiset<Feuille>::iterator it;
//                it = list_leafs.begin();
//                minleaf[j] = it->get<4> ();
//                list_leafs.clear();

                // If all the leaves in the AND where evaluated and if this AND did not require the considered input data element, the AND is marked as completed
                if ((nb_leaves_evaluated == nb_leaves_per_and[j]) && Need_stream == 0)
                    andCompleted[j] = true;
                //cout<<" probaAndTrue[" <<j<<"] : "<<probaAndTrue[j]<<endl;
                //cout<<"trouve :"<<trouve<<endl;
            }

            // Computation of the probability of success of the leaves that precede the minleaf in its own AND
            // The minleaf is the FIRST leaf (in the evaluation order) in the AND that requires the considered input data element
            //            //Calcul de la probabilite du succes des feuilles qui precede la minleaf dans son AND,
            //            //la minleaf c'est la feuille qui peut charger la stream et qui a un nb_data_recup>=nb_recup
            for (int k = 0; k < nb_ands; k++)
            {
                probaPrecendentNeedleaf[k] = 1;
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
                            probaPrecendentNeedleaf[j] *= DNFTree[j][i].proba;
                        }
                    }//for i
                }
                if (DEBUG == 1)
                {
                    cout << "probaPrecendentNeedleaf[" << j << "] : "
                    << probaPrecendentNeedleaf[j] << endl;
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
                    probaNeedingAndsFalse *= (1 - probaPrecendentNeedleaf[j]);
                    if (DEBUG) cout << "\t\t\t" << probaPrecendentNeedleaf[j] << " (" << j << ")" << endl;
                }
            }

            if (DEBUG == 1)
            {
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }

            // If none of the preceding leaves required the considered input data element
            //            //Le cas si l'element e est un nouveau element  charger (trouve =0 veut dire on n'a pas trouv que e peut tre charg quelque part)
            if (trouve == 0)
            {
                Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeafTrue * streamCost[stream];
                if (DEBUG)
                cout << "\tNF\t" << probaCompletedAndsFalse << "*" << probaPrecendentLeafTrue << endl;
                if (DEBUG == 1)
                {
                    cout << "trouve :" << trouve << " ,probaPrecendentLeafTrue :"
                    << probaPrecendentLeafTrue << " ,leafcost :"
                    << probaCompletedAndsFalse * probaPrecendentLeafTrue
                    * streamCost[stream] << "nb_recup :" << nb_recup
                    << endl;
                }
            }
            else
            {
            	// One of the leaves of the AND including the target leaf, and preceding the target leaf in the evaluation order, required the considered input data element
            	// Therefore, each time the target leaf is evaluated the require input data element has always been loaded and the cost is null.
            	//                //Le cas o l'element e peut tre charger par le AND de la feuille tudie
                if (Needingand[the_and] == true)
                {
                    Leaf_cost += 0;
                    if (DEBUG)
                    	cout << "\t0" << endl;
                    if (DEBUG == 1)
                    {
                        cout << "trouve :" << trouve << " ,leafcost :" << 0
                        << "nb_recup :" << nb_recup << endl;
                    }
                }
                //               //                Le cas o l'element e peut tre charger par les autres NeedingAND
                // The remaining case: the considered input data element could have been loaded by at least one AND, but not by the one including the target leaf
                else
                {
                	//                    //Le cas o l'element e peut tre charger par les autres NeedingAND
                    Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeafTrue) * streamCost[stream];
                    if (DEBUG)
                    cout << "\tF\t" << probaNeedingAndsFalse << "*" << probaCompletedAndsFalse << "*" << probaPrecendentLeafTrue << endl;
                    if (DEBUG == 1)
                    {
                        cout << "trouve :" << trouve << " ,leafcost :"
                        << probaNeedingAndsFalse * (probaCompletedAndsFalse
                                                    * probaPrecendentLeafTrue) * streamCost[stream]
                        << " ,nb_recup :" << nb_recup << endl;
                    }
                }
            }
            //cout << "\tLeaf_cost= " << Leaf_cost << endl;
        }
        }
        // We mark the considered leaf as have been evaluated
        DNFTree[the_and][the_leaf].full_eval = 1;
        // We add the cost of the target leaf to the global cost computed so far
        Global_cost += Leaf_cost;
        if (DEBUG)
        cout<<"!!!!!!!Global_cost :"<<Global_cost << " (" << Leaf_cost << ")" << endl;

    }

    delete [] probaPrecendentNeedleaf;
    delete [] probaAndTrue;
    delete [] minleaf;
    delete [] Needingand;
    delete [] andCompleted;
    //cout << Global_cost << endl;
    return (Global_cost);
}


// Optimized version of the function as above, but working on an array description of the order rather than on a vector description
long double
Cost4Arrays_optimized(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, int nb_streams, long double * streamCost,
		int nb_leaves, int * and_id, int * leaf_id)
{
//	for(int leaf_rank=0; leaf_rank<nb_leaves; leaf_rank++)
//	{
//		// Retrieval of the identity and characteristics of the ``target'' leaf
//		int the_and = and_id[leaf_rank];
//		int the_leaf = leaf_id[leaf_rank];
//		int nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup;
//		int stream = DNFTree[the_and][the_leaf].stream;
//		long double proba = DNFTree[the_and][the_leaf].proba;
//		cout << the_and << "\t" << the_leaf << "\t" << stream << "\t" << nb_data_recup << "\t" << proba << endl;
//	}

    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
//    int nb_data_recup;
//    int stream;
//    long double proba;
 //   int nb_leaves_evaluated;
    //vector<leaf_place>::iterator it;

    //long double * probaPrecendentNeedleaf = new long double[nb_ands];

    // Data structure to record how leaves of each AND have been evaluated so far
    // and which ANDs have been fully evaluated so far
    int  * nb_evaluated_leaves = new int [nb_ands];
    bool * andCompleted = new bool[nb_ands];
    for (int k = 0; k < nb_ands; k++){
    	nb_evaluated_leaves[k] = 0;
        andCompleted[k] = false;
    }

//    // Computing the number of considered streams
//    int nb_streams = 1;
//    for(int AND_rank = 0; AND_rank < nb_ands; AND_rank++){
//    	for(int leaf_rank=0; leaf_rank < nb_leaves_per_and[AND_rank]; leaf_rank++){
//    		if (nb_streams < 1+DNFTree[AND_rank][leaf_rank].stream){
//    			nb_streams = 1+DNFTree[AND_rank][leaf_rank].stream;
//    		}
//    	}
//    }
    // Data structure to record the maximum number of elements per stream
    int * max_elements_per_stream = new int [nb_streams];
    for(int stream_id=0; stream_id<nb_streams; stream_id++){
    	max_elements_per_stream[stream_id] = 0;
    }
    for(int AND_rank = 0; AND_rank < nb_ands; AND_rank++){
    	for(int leaf_rank=0; leaf_rank < nb_leaves_per_and[AND_rank]; leaf_rank++){
    		for(int stream=0; stream<nb_streams; stream++){
    			if(max_elements_per_stream[stream] < DNFTree[AND_rank][leaf_rank].nb_data_recup[stream]){
    				max_elements_per_stream[stream] = DNFTree[AND_rank][leaf_rank].nb_data_recup[stream];
    			}
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
//    bool * Needingand = new bool[nb_ands];
//    for (int k = 0; k < nb_ands; k++)
//    {
//        Needingand[k] = false;
//    }

 //   int Need_stream = 0;
//    int * minleaf = new int[nb_ands];
//    for (int k = 0; k < nb_ands; k++)
//    {
//        minleaf[k] = -1;
//    }

    // Computation of each AND to evaluate to true
    long double * probaAndTrue = new long double[nb_ands];
    for (int k = 0; k < nb_ands; k++){
    	probaAndTrue[k] = 1;
//        for (int i = 0; i < nb_leaves_per_and[k]; i++){
//        	probaAndTrue[k] *= DNFTree[k][i].proba;
//        }
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

    long double probaPrecendentLeafTrue = 1;

    // The full_eval field of each leaf is initialized to 0
    //    //Mise  O de tous les full_eval des feuilles de l'arbre
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
        for(int stream=0; stream<nb_streams; stream++){
        int nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup[stream];
        //stream = DNFTree[the_and][the_leaf].stream;
        //proba = DNFTree[the_and][the_leaf].proba;
        // Initialization of the leaf cost
        Leaf_cost = 0;

        if (DEBUG == 1)
        {
            cout << "Feuille with and :" << the_and << "  and leaf_place :"
            << the_leaf << endl;
        }

        // If the AND the target leaf belongs to is evaluated, computation of the probability that the target leaf itself is evaluated
        // This is the product of the probability of success of this AND leaves that are executed (in the order) before the target leaf
//        probaPrecendentLeafTrue = 1;
//        for (int i = 0; i < nb_leaves_per_and[the_and]; i++)
//        {
//            if (DNFTree[the_and][i].full_eval == 1)
//            {
//                probaPrecendentLeafTrue *= DNFTree[the_and][i].proba;
//            }
//        }
//        if (DEBUG == 1)
//        {
//            cout << "probaPrecendentLeafTrue : " << probaPrecendentLeafTrue
//            << endl;
//        }
//        probaPrecendentLeafTrue = proba_leaf_evaluated[the_and][the_leaf];
        // We consider one by one all the input data elements the target leaf depends upon
//        int nb_recup = 0;
        for (int e = 0; e < nb_data_recup; e++)
        {
 //       	cout << the_and << "\t" << the_leaf << "\t" << stream << "\t" << e << endl;
 //           nb_recup++;
            // Initializations...
//            for (int k = 0; k < nb_ands; k++)
//            {
//                andCompleted[k] = false;
// //               Needingand[k] = false;
//            }

          //  int trouve = 0;
            // Loop on all the ANDs
//            for (int j = 0; j < nb_ands; j++)
//            {
//                nb_leaves_evaluated = 0;
//                Need_stream = 0;
//                int eval_rank = INT_MAX;
//                // Loop on all the leaves of the considered AND
//                for (int i = 0; i < nb_leaves_per_and[j]; i++)
//                {
//                	// If the leaf had been evaluated = precedes (directly or not) the target leaf in the evaluation order
//                	if (DNFTree[j][i].full_eval == 1)
//                    {
//                        nb_leaves_evaluated++;
//                        // If the considered leaf requires the considered element of the target leaf
//                        if (DNFTree[j][i].stream == stream
//                            && DNFTree[j][i].nb_data_recup >= nb_recup)
//                        {
//                        	// The considered AND is marked as requiring the considered data input element
//                        	Need_stream = 1;
// //                           Needingand[j] = true;
//                            // The characteristics of the leaf are recorded if this is (so far) the first leaf of this AND,
//                            // in the evaluation order, that requires the considered input data element.
//                            if(DNFTree[j][i].eval_order < eval_rank){
//                            	eval_rank = DNFTree[j][i].eval_order;
//                            	minleaf[j] = i;
//                            }
//
//                       //     trouve = 1;
//                        }
//                    }
//                }
//
//
//                // If all the leaves in the AND where evaluated and if this AND did not require the considered input data element, the AND is marked as completed
////                if ((nb_leaves_evaluated == nb_leaves_per_and[j]) && Need_stream == 0)
////                    andCompleted[j] = true;
//            }

            // Computation of the probability of success of the leaves that precede the minleaf in its own AND
            // The minleaf is the FIRST leaf (in the evaluation order) in the AND that requires the considered input data element
//            for (int k = 0; k < nb_ands; k++){
//                probaPrecendentNeedleaf[k] = 1;
//            }

            // Loop over all the ANDs
//            for (int j = 0; j < nb_ands; j++)
//            {
//            	// If the considered AND is not the AND including the target leaf, but if it requires the considered input data element
//                if ((AND_needs_data[j][stream][e] == true) && (j != the_and)){
////                if ((Needingand[j] == true) && (j != the_and)){
//                	// Loop over all the leaves of the considered AND
//                	for (int i = 0; i < nb_leaves_per_and[j]; i++){
//                		// If the leaf was evaluated, and preceded the minleaf
//                		if ((DNFTree[j][i].full_eval == 1)
//                            && (DNFTree[j][i].eval_order
//                                < DNFTree[j][minleaf[j]].eval_order)){
//                            probaPrecendentNeedleaf[j] *= DNFTree[j][i].proba;
//                        }
//                    }//for i
//                }
////                if (DEBUG == 1){
////                    cout << "probaPrecendentNeedleaf[" << j << "] : "
////                    << probaPrecendentNeedleaf[j] << endl;
////                }
//            }//for j


            // Compute the probability that all ANDs completely evaluated and not requiring the considered input data elements were all false
            long double probaCompletedAndsFalse = 1;
            for (int j = 0; j < nb_ands; j++)
            {
//                if (andCompleted[j] == true){
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
//                if ((Needingand[j] == true) && (j != the_and)){
//                    probaNeedingAndsFalse *= (1 - probaPrecendentNeedleaf[j]);
                    probaNeedingAndsFalse *= (1 - proba_data_read[j][stream][e]);
 //                   cout << "Potential problem: " << probaPrecendentNeedleaf[j] << "\t" << proba_data_read[j][stream][e] << endl;
                }
            }

            if (DEBUG == 1){
                cout << " probaNeedingAndsFalse" << probaNeedingAndsFalse << endl;
            }

            probaPrecendentLeafTrue = proba_leaf_evaluated[the_and][the_leaf];

            // If none of the preceding leaves required the considered input data element
            if (found[stream][e] == false){
//            if (trouve == 0){
                Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeafTrue * streamCost[stream];
//                if (DEBUG == 1){
//                    cout << "trouve :" << trouve << " ,probaPrecendentLeafTrue :"
//                    << probaPrecendentLeafTrue << " ,leafcost :"
//                    << probaCompletedAndsFalse * probaPrecendentLeafTrue
//                    * streamCost[stream] << "nb_recup :" << nb_recup
//                    << endl;
//                }
            }
            else
            {
            	// One of the leaves of the AND including the target leaf, and preceding the target leaf in the evaluation order, required the considered input data element
            	// Therefore, each time the target leaf is evaluated the require input data element has always been loaded and the cost is null.
            	if (AND_needs_data[the_and][stream][e] == true){
//                if (Needingand[the_and] == true){
                    Leaf_cost += 0;
//                    if (DEBUG == 1)
//                    {
//                        cout << "trouve :" << trouve << " ,leafcost :" << 0
//                        << "nb_recup :" << nb_recup << endl;
//                    }
                }
                // The remaining case: the considered input data element could have been loaded by at least one AND, but not by the one including the target leaf
                else
                {
                    Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeafTrue) * streamCost[stream];
//                    if (DEBUG == 1)
//                    {
//                        cout << "trouve :" << trouve << " ,leafcost :"
//                        << probaNeedingAndsFalse * (probaCompletedAndsFalse
//                                                    * probaPrecendentLeafTrue) * streamCost[stream]
//                        << " ,nb_recup :" << nb_recup << endl;
//                    }
                }
            }
        }
        }
        // We mark the considered leaf as have been evaluated
        DNFTree[the_and][the_leaf].full_eval = 1;
        // We record that the AND loaded the data
        for(int stream=0; stream<nb_streams; stream++){
        	for(int element = 0; element < DNFTree[the_and][the_leaf].nb_data_recup[stream]; element++){
        		if(AND_needs_data[the_and][stream][element]==false){
        			proba_data_read[the_and][stream][element] = proba_leaf_evaluated[the_and][the_leaf];
        			AND_needs_data[the_and][stream][element] = true;
        			found[stream][element] = true;
        		}
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

//    delete [] probaPrecendentNeedleaf;
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
//    delete [] minleaf;
//    delete [] Needingand;
    delete [] andCompleted;
    delete [] nb_evaluated_leaves;
    //cout << Global_cost << endl;
    return (Global_cost);
}

// Optimized version of the function as above, but working on an array description of the order rather than on a vector description
long double
Cost4Arrays_stripped(leaf ** DNFTree, int nb_ands, int * nb_leaves_per_and, long double * streamCost,
		int nb_leaves, int rank_first_leaf, int rank_last_leaf, int * and_id, int * leaf_id, int nb_streams, int * max_elements_per_stream,
		bool *** AND_needs_data, long double *** proba_data_read, long double * probaAndTrue, bool * andCompleted)
{

//	cout << "DEBUG\t" << proba_data_read[0][7][0] << endl;

    //Declaration of all data structure needed
    long double Global_cost = 0;
    long double Leaf_cost = 0;
//    int nb_data_recup;
//    int stream;
//    long double proba;

//    // Data structure to record which data input elements have already been encountered
//    bool ** found = new bool * [nb_streams];
//	for(int stream_id=0; stream_id<nb_streams; stream_id++){
//		found[stream_id] = new bool [max_elements_per_stream[stream_id]];
//		for(int nb_streams_elements=0; nb_streams_elements < max_elements_per_stream[stream_id]; nb_streams_elements++){
//			found[stream_id][nb_streams_elements] = false;
//		}
//	}

    long double probaPrecendentLeafTrue = 1;

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
        Leaf_cost = 0;

        for(int stream=0; stream<nb_streams; stream++){
        	int nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup[stream];
        	//stream = DNFTree[the_and][the_leaf].stream;
        	//proba = DNFTree[the_and][the_leaf].proba;
        	// Initialization of the leaf cost

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

        		//            // If none of the preceding leaves required the considered input data element
        		//            bool found = AND_needs_data[0][stream][e];
        		//            int test_and = 1;
        		//            while ((found == false) && (tested_and < nb_ands)){
        		//            	found = AND_needs_data[tested_and][stream][e];
        		//            	tested_and++;
        		//            }

        		// One of the leaves of the AND including the target leaf, and preceding the target leaf in the evaluation order, required the considered input data element
        		// Therefore, each time the target leaf is evaluated the require input data element has always been loaded and the cost is null.
        		if (AND_needs_data[the_and][stream][e] == true){
        			Leaf_cost += 0;
        			if (DEBUG) cout << "\t" << 0 << endl;
        		}
        		else{
        			if (found==false){
        				//            if (found[stream][e] == false){
        				Leaf_cost += probaCompletedAndsFalse * probaPrecendentLeafTrue * streamCost[stream];
        				if (DEBUG) cout << "\tNF\t" << probaCompletedAndsFalse << "*" << probaPrecendentLeafTrue << endl;
        			}
        			// The remaining case: the considered input data element could have been loaded by at least one AND, but not by the one including the target leaf
        			else
        			{
        				Leaf_cost += probaNeedingAndsFalse * (probaCompletedAndsFalse * probaPrecendentLeafTrue) * streamCost[stream];
        				if (DEBUG) cout << "\tF\t" << probaNeedingAndsFalse << "*" << probaCompletedAndsFalse << "*" << probaPrecendentLeafTrue << endl;
        			}
        		}
        	}
        }
        // We mark the considered leaf as have been evaluated
        DNFTree[the_and][the_leaf].full_eval = 1;
        // We record that the AND loaded the data
        for(int stream=0; stream<nb_streams; stream++){
        	for(int element = 0; element < DNFTree[the_and][the_leaf].nb_data_recup[stream]; element++){
        		if(AND_needs_data[the_and][stream][element]==false){
        			proba_data_read[the_and][stream][element] = probaPrecendentLeafTrue;
        			AND_needs_data[the_and][stream][element] = true;
        			//       	found[stream][element] = true;
        		}
        	}
        }
        probaPrecendentLeafTrue *= DNFTree[the_and][the_leaf].proba;
        //    	cout << "DEBUG\t" << proba_data_read[0][7][0] << endl;
        // We add the cost of the target leaf to the global cost computed so far
        Global_cost += Leaf_cost;
        //        cout<<"Global_cost :"<<Global_cost << " (" << Leaf_cost << ")\t[" << stream << "|" << nb_data_recup << "]" << endl;
    }


    //    for(int stream_id=0; stream_id < nb_streams; stream_id++){
    //    	delete [] found[stream_id];
    //    }
    //    delete [] found;

    //    cout << Global_cost;
    //    for(int leaf_rank=rank_first_leaf; leaf_rank<rank_last_leaf; leaf_rank++)
    //        {
    //        	// Retrieval of the identity and characteristics of the ``target'' leaf
    //            int the_and = and_id[leaf_rank];
    //            int the_leaf = leaf_id[leaf_rank];
    //            cout << "\t" << the_leaf << " (";
    //            for(int stream=0; stream<nb_streams; stream++){
    //            	int nb_data_recup = DNFTree[the_and][the_leaf].nb_data_recup[stream];
    //            	cout << " " << nb_data_recup;
    //            }
    //        }
    //    cout << endl;
     return (Global_cost);
}

//void sillykernel(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
//		long double * streamCost, int and_id, long double & bestcost,
//		vector<leaf_place> & final_order){
//
//	for(int leaf_id=0; leaf_id<nb_leaves_per_and[and_id]; leaf_id++){
//		final_order.push_back(leaf_place(and_id, leaf_id));
//	}
//	bestcost = Cost(DNFTree, nb_ands, nb_leaves_per_and, nb_streams, streamCost, final_order);
//}


long double MultiStreamGreedy_kernel(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
		long double * streamCost, int and_id, int leaf_id, bool ** dominates,
		long double & base_cost, long double base_proba, long double & order_extension_proba,
		vector<leaf_place> final_order, vector<leaf_place> & order_extension,
		int rec_level)
{
	if (DEBUGMULTIGREEDY>2){
		if(rec_level==1){
			long double verif_cost = Cost(DNFTree, nb_ands, nb_leaves_per_and, nb_streams, streamCost, final_order);
			cout << "Verif:" << base_cost << " =?= " << verif_cost << endl;
		}
	}

	// Evaluation of the cost of the initial order
    vector<leaf_place> best_order = final_order;
    vector<leaf_place> overall_optimal_order_extension = std::vector<leaf_place>();;
	for (vector<leaf_place>::iterator leaf_iterator = order_extension.begin(); leaf_iterator != order_extension.end(); leaf_iterator++){
		int the_leaf = leaf_iterator->get<1> ();
		best_order.push_back(leaf_place(and_id, the_leaf));
		overall_optimal_order_extension.push_back(leaf_place(and_id, the_leaf));
	}
	best_order.push_back(leaf_place(and_id, leaf_id));
	overall_optimal_order_extension.push_back(leaf_place(and_id, leaf_id));

	if (DEBUGMULTIGREEDY){
		for(int i=0; i<rec_level; i++){
			cout << "\t";
		}
		cout << "Level: " << rec_level;
		for (vector<leaf_place>::iterator leaf_iterator = best_order.begin(); leaf_iterator != best_order.end(); leaf_iterator++){
			int the_and = leaf_iterator->get<0> ();
			int the_leaf = leaf_iterator->get<1> ();
			cout << "\t" << the_and << "-" << the_leaf << " (";
			for(int stream=0; stream<nb_streams; stream++){
				cout << " " << DNFTree[the_and][the_leaf].nb_data_recup[stream];
			}
			cout << ")";
		}
		// cout << endl;
	}

	long double cost_simplest_extension = Cost(DNFTree, nb_ands, nb_leaves_per_and, nb_streams, streamCost, best_order);
	long double cost_best_solution = cost_simplest_extension;
	long double proba_of_best_extension = DNFTree[and_id][leaf_id].proba;
	long double best_ratio = (cost_simplest_extension-base_cost)/(1-base_proba*proba_of_best_extension);
	if (best_ratio < 0){
		cout << endl;
		cout << "cost_simplest_extension=" << cost_simplest_extension << endl;
		cout << "base_cost=" << base_cost << endl;
		cout << "proba=" << base_proba*DNFTree[and_id][leaf_id].proba << endl;
		abort();
	}
	if (DEBUGMULTIGREEDY){ cout << "\t" << best_ratio << "\t(" << cost_best_solution << ")"<< endl;}
	//long double proba_of_best_extension = base_proba*DNFTree[and_id][leaf_id].proba;
	vector<leaf_place> optimal_order_extension = overall_optimal_order_extension;

	// We consider all the possible extensions of this initial order
	for(int next_leaf_id=0; next_leaf_id<nb_leaves_per_and[and_id]; next_leaf_id++){
		if (dominates[next_leaf_id][leaf_id]){
			vector<leaf_place> order_further_extension = overall_optimal_order_extension;
			//order_further_extension.push_back(leaf_place(and_id, next_leaf_id));

			vector<leaf_place> further_order_extension = std::vector<leaf_place>();
			long double proba_of_extension = 1;
			long double this_cost = MultiStreamGreedy_kernel(DNFTree, nb_streams, nb_ands, nb_leaves_per_and,
					streamCost, and_id, next_leaf_id, dominates,
					base_cost, base_proba*DNFTree[and_id][leaf_id].proba, proba_of_extension,
					final_order, order_further_extension, rec_level+1);
			long double this_proba = DNFTree[and_id][leaf_id].proba*proba_of_extension;
			long double this_ratio = (this_cost-base_cost)/(1-base_proba*this_proba);
			if(this_ratio < best_ratio){
				best_ratio = this_ratio;
				cost_best_solution = this_cost;
				proba_of_best_extension = this_proba;
				optimal_order_extension = order_further_extension;
			}
			if (DEBUGMULTIGREEDY){
				for(int i=0; i<rec_level; i++){
					cout << "\t";
				}
				cout << best_ratio << "\t (" << cost_best_solution << ")" << endl;
			}
		}
	}

	// Copying the best solution
//	for (vector<leaf_place>::iterator leaf_iterator = optimal_order_extension.begin(); leaf_iterator != optimal_order_extension.end(); leaf_iterator++){
//		int leaf_id = leaf_iterator->get<1> ();
//		order_extension.push_back(leaf_place(and_id, leaf_id));
//	}
	order_extension = optimal_order_extension;
	order_extension_proba = proba_of_best_extension;
	return cost_best_solution;
}

void MultiStreamGreedy(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
		long double * streamCost, int and_id, long double & bestcost,
		vector<leaf_place> & final_order){

	// Computation of all domination relations
	bool ** dominates = new bool * [nb_leaves_per_and[and_id]];
	bool ** dominates_directly = new bool * [nb_leaves_per_and[and_id]];
	bool * notyetscheduled = new bool [nb_leaves_per_and[and_id]];
	bool * source_leaf = new bool [nb_leaves_per_and[and_id]];
	for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
		dominates[first_leaf] = new bool [nb_leaves_per_and[and_id]];
		dominates_directly[first_leaf] = new bool [nb_leaves_per_and[and_id]];
		notyetscheduled[first_leaf] = true;
		source_leaf[first_leaf] = true;
		for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
			dominates[first_leaf][second_leaf] = false;
			dominates_directly[first_leaf][second_leaf] = false;
		}
	}
	int n_notscheduled = nb_leaves_per_and[and_id];

	long double min_ratio = DBL_MAX;
	long double cost_optimal_order_extension = DBL_MAX;
	long double base_cost = bestcost;

	if (DEBUGMULTIGREEDY){
		cout << "Entering MultiStreamGreedy" << endl;
		for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
			cout << " " << first_leaf << " (";
			for(int stream_id=0; stream_id < nb_streams; stream_id++){
				cout << " " << DNFTree[and_id][first_leaf].nb_data_recup[stream_id] ;
			}
			cout << ") ";
		}
			cout << endl;
	}

	while(n_notscheduled > 0){
		if (DEBUGMULTIGREEDY) cout << "AND= " << and_id << " New iteration of while loop: " << n_notscheduled << " leaves remaining." << endl;
		//
		// Computation of the dominance relationship
		//
		for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
			source_leaf[first_leaf] = true;
		}
		for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
			if(notyetscheduled[first_leaf]){
				for(int second_leaf=first_leaf+1; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
					if(notyetscheduled[second_leaf]){
						bool first_dominate_second = true;
						bool second_dominate_first = true;
						for(int stream_id=0; stream_id < nb_streams; stream_id++){
							if (DNFTree[and_id][first_leaf].nb_data_recup[stream_id] > DNFTree[and_id][second_leaf].nb_data_recup[stream_id]){
								second_dominate_first = false;
							}
							else{
								if (DNFTree[and_id][first_leaf].nb_data_recup[stream_id] < DNFTree[and_id][second_leaf].nb_data_recup[stream_id]){
									first_dominate_second = false;
								}
							}
						}
						if (second_dominate_first && first_dominate_second){
							// The two have identical requirements, the order has no importance
							if(DNFTree[and_id][first_leaf].proba < DNFTree[and_id][second_leaf].proba){
								dominates[second_leaf][first_leaf] = true;
								dominates[first_leaf][second_leaf] = false;
								source_leaf[second_leaf] = false;
//								cout << second_leaf << " not source (first=" << first_leaf << " second=" << second_leaf << ")" << endl;
							}
							else{
								dominates[second_leaf][first_leaf] = false;
								dominates[first_leaf][second_leaf] = true;
								source_leaf[first_leaf] = false;
//								cout << first_leaf << " not source (first=" << first_leaf << " second=" << second_leaf << ")" << endl;
							}
						}
						else{
//							cout <<	first_leaf << endl;
//							cout << "\t" << second_leaf << endl;
//							cout << "\t\t" << first_dominate_second << endl;
							dominates[first_leaf][second_leaf] = first_dominate_second;
							dominates[second_leaf][first_leaf] = second_dominate_first;
							if(first_dominate_second){
								source_leaf[first_leaf] = false;
//								cout << first_leaf << " not source (first=" << first_leaf << " second=" << second_leaf << ") [OLD]" << endl;
							}
							else if(second_dominate_first){
								source_leaf[second_leaf] = false;
//								cout << second_leaf << " not source (first=" << first_leaf << " second=" << second_leaf << ") [OLD]" << endl;
							}
						}
					}
				}
			}
		}

	//	cout << "Not Yet Scheduled leaves" << endl;

//		cout << " dominancy with transitive edges" << endl;
//		for(int leaf_id=0; leaf_id < nb_leaves_per_and[and_id]; leaf_id++){
//			cout << leaf_id << " scheduled? " << notyetscheduled[leaf_id] << " source? " << source_leaf[leaf_id] << "\t dominance";
//			for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
//				cout << " " << dominates[leaf_id][second_leaf];
//			}
//			cout << endl;
//		}

		//
		// Removal of the transitive edges in the dominance relationship
		//
		// Initialization
		for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
			for(int second_leaf=first_leaf+1; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
				dominates_directly[first_leaf][second_leaf] = false;
			}
		}
		// Check whether the second_leaf dominates the first_leaf directly (and not through transitivity)
		for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
			if(notyetscheduled[first_leaf]){
				for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
					if((first_leaf!=second_leaf) && notyetscheduled[second_leaf] && dominates[first_leaf][second_leaf]){
						// We check whether there exists a "middle" leaf that dominates second_leaf and is dominated by first_leaf
						//cout << "\tConsidering dominance " << first_leaf << " >= " << second_leaf << endl;
						bool no_middle_leaf = true;
						//cout << "\t\t";
						for(int middle_leaf=0; middle_leaf < nb_leaves_per_and[and_id]; middle_leaf++){
							if ((middle_leaf!=first_leaf)&&(middle_leaf!=second_leaf)&&notyetscheduled[middle_leaf]&&
									dominates[middle_leaf][second_leaf] && dominates[first_leaf][middle_leaf]){
								//cout << endl << "\t\t Middle leaf: " << middle_leaf << endl;
								no_middle_leaf = false;
							}
							//cout << no_middle_leaf << " ";
						}
						//cout << endl;
						dominates_directly[first_leaf][second_leaf] = no_middle_leaf;
					}
				}
			}
		}

//		cout << " dominancy WITHOUT transitive edges" << endl;
//		for(int leaf_id=0; leaf_id < nb_leaves_per_and[and_id]; leaf_id++){
//			cout << leaf_id << " scheduled? " << notyetscheduled[leaf_id] << " source? " << source_leaf[leaf_id] << "\t dominance";
//			for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
//				cout << " " << dominates_directly[leaf_id][second_leaf];
//			}
//			cout << endl;
//		}

		// TODO: simplification of the distance relationship: erasing the transitive edges!

//		for(int leaf_id=0; leaf_id < nb_leaves_per_and[and_id]; leaf_id++){
//			cout << leaf_id << ": ";
//			for(int stream_id=0; stream_id<nb_streams; stream_id++){
//				cout << " " << DNFTree[and_id][leaf_id].nb_data_recup[stream_id];
//			}
//			cout << "\t(" << DNFTree[and_id][leaf_id].proba << ")";
//			cout << endl;
//		}
//
//		for(int leaf_id=0; leaf_id < nb_leaves_per_and[and_id]; leaf_id++){
//			cout << leaf_id << " scheduled? " << notyetscheduled[leaf_id] << " source? " << source_leaf[leaf_id] << "\t dominance";
//			for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
//				cout << " " << dominates[leaf_id][second_leaf];
//			}
//			cout << endl;
//		}



		min_ratio = DBL_MAX;
		cost_optimal_order_extension = DBL_MAX;
        vector<leaf_place> optimal_order_extension;

		for(int leaf_id=0; leaf_id < nb_leaves_per_and[and_id]; leaf_id++){
			//cout << leaf_id << "\t" << notyetscheduled[leaf_id] << "\t" << source_leaf[leaf_id] << endl;
			if(notyetscheduled[leaf_id] && source_leaf[leaf_id]){
				//cout << "\tLEAF CONSIDERED" << endl;
				vector<leaf_place> order_extension = std::vector<leaf_place>();
				//order_extension.push_back(leaf_place(and_id, leaf_id));
				long double order_extension_proba = -1;
				long double this_cost = MultiStreamGreedy_kernel(DNFTree, nb_streams, nb_ands, nb_leaves_per_and,
						streamCost, and_id, leaf_id, dominates_directly,
						base_cost, 1, order_extension_proba,
						final_order, order_extension, 1);

				long double this_ratio = (this_cost-base_cost) / (1-order_extension_proba);
				if(this_ratio < min_ratio){
					min_ratio = this_ratio;
					cost_optimal_order_extension = this_cost;
					//optimal_order_extension_proba = order_extension_proba;
					optimal_order_extension = order_extension;
				}
			}
		}

		//TODO: detect the leaves whose arguments have all been retrieved because of scheduled leaves

		// The best order extension is appended to the leaf order
		if (DEBUGMULTIGREEDY>2){
			cout << "Best solution: ";
		}
		vector<leaf_place>::iterator leaf_iterator;
		for (leaf_iterator = optimal_order_extension.begin(); leaf_iterator != optimal_order_extension.end(); leaf_iterator++){
			int leaf_id = leaf_iterator->get<1> ();
			final_order.push_back(leaf_place(and_id, leaf_id));
			notyetscheduled[leaf_id] = false;
			//source_leaf[leaf_id] = false;
			for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
				dominates[leaf_id][second_leaf] = false;
				dominates[second_leaf][leaf_id] = false;

			}
			n_notscheduled--;
			if (DEBUGMULTIGREEDY>2){
				cout << "\t" << leaf_id;
			}
		}
		if (DEBUGMULTIGREEDY>2){
			cout << " : " << min_ratio << "\t(" << cost_optimal_order_extension  << ")"<< endl;
		}
		base_cost = cost_optimal_order_extension;
		if (DEBUGMULTIGREEDY>2){
			for(int second_leaf=0; second_leaf < nb_leaves_per_and[and_id]; second_leaf++){
				cout << "\t" << notyetscheduled[second_leaf];
			}
			cout << endl;
		}
	}



//	for(int leaf_id=0; leaf_id<nb_leaves_per_and[and_id]; leaf_id++){
//		final_order.push_back(leaf_place(and_id, leaf_id));
//	}

	// Deallocation
	for(int first_leaf=0; first_leaf < nb_leaves_per_and[and_id]; first_leaf++){
		delete [] dominates[first_leaf];
		delete [] dominates_directly[first_leaf];
	}
	delete [] dominates;
	delete [] dominates_directly;
	delete [] notyetscheduled;
	delete [] source_leaf;

	bestcost = base_cost;
}

//
//void
//newglouton(leaf ** DNFTree, int nb_streams, int nb_ands, int * nb_leaves_per_and,
//           long double * streamCost, int & leaf_rest, long double & bestcost,
//           std::vector<multiset<Feuille> > & disjoint_set,
//           vector<leaf_place> & final_order)
//{
//    long double proba_tot;
//    long double cost;
//    long double ratio;
//    long double min = DBL_MAX;
//    int stream_min = 0;
//    int recup_min = 1;
//    long double proba_min;
//    int recup;
//    long double cost_min = 0;
//    // long double bestcostprec=bestcost;
//
//    //int leaf_rest=nb_leaves_per_and[2];
//
//    if (leaf_rest == 0)
//    {
//        if (DEBUG1)
//        {
//            cout << "Fin_glouton, bestcost : " << bestcost << endl;
//            vector<leaf_place>::iterator it0;
//            for (it0 = final_order.begin(); it0 < final_order.end(); it0++)
//            {
//                cout << " and :" << it0->get<0> () << " leaf_place :"
//                << it0->get<1> () << endl;
//            }
//
//        }
//        // FV: commented line because the return value of newglouton is never used in the code
//        //        return bestcost;
//    }
//
//    else
//    {
//        vector<leaf_place> optimal_order;
//        vector<leaf_place> evaluation_order;
//        multiset<Feuille>::iterator it;
//        vector<leaf_place> order_prec;
//        //order_prec=final_order;
//        if (DEBUG1 == 1)
//        {
//            cout << "**********Debut newglouton :" << endl;
//        }
//        for (int s = 0; s < nb_streams; s++)
//        {
//            cost = 0;
//            proba_tot = 1;
//            recup = 0;
//
//            order_prec = final_order;
//
//            for (it = (disjoint_set[s]).begin(); it != (disjoint_set[s]).end(); it++)
//            {
//                if (DEBUG1 == 1)
//                {
//                    cout << "feuille : " << it->get<3> () << "," << it->get<4> () << ": "
//                    		<< it->get<0> () << "," << it->get<1> ()
//                    << endl;
//                }
//                evaluation_order.push_back(leaf_place(it->get<3> (), it->get<4> ()));
//                order_prec.push_back(leaf_place(it->get<3> (), it->get<4> ()));
//                /*
//                 vector< leaf_place >::iterator it6;
//                 for (it6=order_prec.begin(); it6<order_prec.end(); it6++)
//                 cout << "order_prec0 : " << it6->get<0> ()<<" ,order_prec1 :" << it6->get<1> ()<<endl;
//                 */
//                cost
//                = Cost(DNFTree, nb_ands, nb_leaves_per_and, streamCost, order_prec)
//                - bestcost;
//                if (DEBUG1 == 1)
//                {
//                    cout << "bestcost :" << bestcost << endl;
//                    cout << "cost :" << Cost(DNFTree, nb_ands, nb_leaves_per_and,
//                                             streamCost, order_prec) << " -  " << bestcost << " = "
//                    << cost << endl;
//                }
//
//                proba_tot *= it->get<2> ();
//                //cout <<" ,proba_tot :"<<proba_tot;
//
//                //calcul du ratio de chaque suite de feuilles qui est ordonne par ordre croissant des couts de rcuperation.
//                ratio = cost / (1 - proba_tot);
//                if (DEBUG1 == 1)
//                {
//                    cout << "Ratio :" << ratio << endl;
//                }
//                if ( (ratio < min)  || (ratio <= min &&  ( evaluation_order.size() > optimal_order.size() )) )
//                {
//                    min = ratio;
//                    cost_min = cost;
//                    proba_min = proba_tot;
//                    stream_min = s;
//                    recup_min = it->get<0> ();
//                    optimal_order = evaluation_order;
//                }
//
//            }
//
//            evaluation_order = std::vector<leaf_place>();
//            //il faut rinitialiser bestcost
//            // bestcost=bestcostprec;@
//        }
//
//        vector<leaf_place>::iterator it2;
//        for (it2 = optimal_order.begin(); it2 != optimal_order.end(); it2++)
//        {
//            final_order.push_back(leaf_place(it2->get<0> (), it2->get<1> ()));
//            leaf_rest--;
//            //cout<<"leaf_rest :"<< leaf_rest<<endl;
//        }
//        bestcost += cost_min;
//        if (DEBUG1 == 1)
//        {
//            cout << " ratio_min :" << min << endl;
//            cout << " bestcost :" << bestcost << endl;
//            vector<leaf_place>::iterator it3;
//            for (it3 = final_order.begin(); it3 < final_order.end(); it3++)
//            {
//                cout << " and :" << it3->get<0> () << " leaf_place :"
//                << it3->get<1> () << endl;
//            }
//        }
//        //Mise a jour des feuilles
//        multiset<Feuille>::iterator it1;
//
//        it1 = (disjoint_set[stream_min]).begin();
//        while(it1!= (disjoint_set[stream_min]).end()){
//            if ((it1->get<0> ()) <= recup_min)
//            {
//            	multiset<Feuille>::iterator copy_it1 = it1;
//            	it1++;
//            	(disjoint_set[stream_min]).erase(copy_it1);
//            }
//            else{
//            	it1++;
//            }
//        }
////        for (it1 = (disjoint_set[stream_min]).begin(); it1!= (disjoint_set[stream_min]).end(); it1++)
////        {
////
////            if ((it1->get<0> ()) <= recup_min)
////            {
////                (disjoint_set[stream_min]).erase(it1);
////            }
////
////        }
//
//        newglouton(DNFTree, nb_streams, nb_ands, nb_leaves_per_and, streamCost,
//                   leaf_rest, bestcost, disjoint_set, final_order);
//
//        //return final_order;
//    }
//
//}




void
argument_processing_for_DNF(int argc, char ** argv)
{
    if (DEBUG)
    {
        cout << "Debut de lancement des heuristiques " << endl;
    }
    
    // Reading the program parameters
    // INDICE de l'arbre:
    double ratio = boost::lexical_cast<double>(argv[3]);

//    int indice= boost::lexical_cast<int>(argv[5]);
    int seed = boost::lexical_cast<int>(argv[5]);

    int nb_streams  = boost::lexical_cast<int>(argv[7]);


    //nombre de fils AND
    int nb_ands = boost::lexical_cast<int>(argv[9]);
    //cout<< "nb_ands= "<< nb_ands << endl;
    int nbmaxleaves = boost::lexical_cast<int>(argv[11]);
    
    //Tableau qui stocke le nombre de feuille pour chaque AND
    int * nb_leaves_per_and = new int[nb_ands];
    for (int j = 0; j < nb_ands; j++)
    {
        nb_leaves_per_and[j] = boost::lexical_cast<int>(argv[13 + j]);
        //cout<< "nb_leaves_per_and["<<j<< "]= "<< nb_leaves_per_and[j] << endl;
    }
    
    //int k = 1;
    
    //cout << "before the reads" << endl;

    int nb_input_data_read = 14+nb_ands;
    leaf ** DNF = new leaf *[nb_ands];
    for (int j = 0; j < nb_ands; j++)
    {
    	DNF[j] = new leaf[nb_leaves_per_and[j]];
    	for (int i = 0; i < nb_leaves_per_and[j]; i++)
    	{
    		//DNF[j][i].nb_streams = 1;
    		//DNF[j][i].stream = new int [DNF[j][i].nb_streams];
    		DNF[j][i].nb_data_recup = new int [nb_streams];
    		if(LEGACY_MODE){
    			for(int k=0; k<nb_streams; k++){
    				DNF[j][i].nb_data_recup[k] = 0;
    			}
    		    //cout << "before stream_id" << endl;
    			int stream_id = boost::lexical_cast<int>(argv[nb_input_data_read]);
    		    //cout << "before nb_data" << endl;
    			int nb_data = boost::lexical_cast<int>(argv[nb_input_data_read + 1]);
    		    //cout << "after nb_data" << endl;
    			DNF[j][i].nb_data_recup[stream_id] = nb_data;
    			nb_input_data_read += 2;
    		}
    		else{
    			for(int k=0; k<nb_streams; k++){
    				//  			DNF[j][i].stream[k] = boost::lexical_cast<int>(argv[nb_input_data_read + 2*k]);
    				//cout<< DNF[j][i].nb_data_recup << endl;
    				//cout << j << "\t" << i << "\t" << k << endl;
    				DNF[j][i].nb_data_recup[k] = boost::lexical_cast<int>(argv[nb_input_data_read + k]);
    				//cout<< DNF[j][i].stream << endl;
    			}
    			nb_input_data_read += nb_streams;
    		}
    		DNF[j][i].proba = boost::lexical_cast<long double>(argv[nb_input_data_read]);
    		nb_input_data_read++;
    		DNF[j][i].full_eval = 0;
    		DNF[j][i].eval_order = 0;
    		//cout<< DNF[j][i].proba << endl
    	}
    }
    
    //cout << "after leaves "  << nb_input_data_read << endl;
    
    if (DEBUG)
    {
        cout << "nb_streams =" << nb_streams << endl;
    }
    long double * streamCost = new long double[nb_streams];
    for (int s = 0; s < nb_streams; s++)
    {
        streamCost[s] = boost::lexical_cast<long double>(argv[nb_input_data_read + 1 + s]);
        //cout << "streamCost: " << streamCost[s] << endl;
    }
    nb_input_data_read += 1+nb_streams;

    //cout << "after stream cost ( " << streamCost[nb_streams-1]  << ")\t" << nb_input_data_read << endl;


    int heuristic_code = boost::lexical_cast<int>(argv[nb_input_data_read+1]);
    bool with_optimal = false;
    bool with_optimal_singlestream = false;
    bool with_progdyn = false;
    bool with_heuristics = false;
	bool with_single_and = false;
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
    	with_optimal = true;
    	with_optimal_singlestream = false;
    	with_progdyn = true;
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
    	with_optimal = true;
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
//    with_progdyn = false;
//	with_optimal_singlestream = false;
//	with_optimal = false;

//    cout << "Sanity check " << heuristic_code ;
//    for (int s = 0; s < nb_streams; s++){
//    	cout << "\t" << streamCost[s];
//    }
//    cout << endl;


    // cout<<"ici"<<endl;
    
    //Affichage de la liste des streams
    //set<int>::iterator it;
    //cout << "mystreams contains:";
    //for ( it=mystreams.begin() ; it != mystreams.end(); it++ )
    //cout << " " << *it << endl;
    
    
    int Sum_max_recup = 0;
    unsigned long int nb_cases = 1;
    unsigned long int previous_nb_cases = 0;
    int int_overflow_for_progdyn = 0;
    
    std::vector<int> vector_max(nb_streams, 0);
    //vecteur qui stocke le max des nombres delements recuperes a partir de chaque stream s
    for (int s = 0; s < nb_streams; s++){
    	vector_max[s] = 0;
    }
    for (int j = 0; j < nb_ands; j++){
    	for (int i = 0; i < nb_leaves_per_and[j]; i++){
    		for(int stream=0; stream<nb_streams; stream++){
    			if (vector_max[stream]< DNF[j][i].nb_data_recup[stream]){
    				vector_max[stream] = DNF[j][i].nb_data_recup[stream];
    			}
    		}
    	}
    }

    for (int s = 0; s < nb_streams; s++){
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
    
//    //************calcul de Sum_max_recup de chaque AND
//
//    std::vector<int> Sum_max_recup_oneand(nb_ands, 0);
//
//    for (int j = 0; j < nb_ands; j++)
//    {
//        Sum_max_recup_oneand[j] = 0;
//    }
//
//    int ** max_recup_oneand = new int *[nb_ands];
//    for (int j = 0; j < nb_ands; j++)
//    {
//        max_recup_oneand[j] = new int[nb_streams];
//        for (int i = 0; i < nb_streams; i++)
//        {
//            max_recup_oneand[j][i] = 0;
//        }
//
//    }
//
//    for (int j = 0; j < nb_ands; j++)
//    {
//
//        for (int s = 0; s < nb_streams; s++)
//        {
//            for (int i = 0; i < nb_leaves_per_and[j]; i++)
//            {
//                if ((DNF[j][i].stream == s) && (max_recup_oneand[j][s]
//                                                < DNF[j][i].nb_data_recup))
//                {
//                    max_recup_oneand[j][s] = DNF[j][i].nb_data_recup;
//                }
//            }
//
//            Sum_max_recup_oneand[j] = Sum_max_recup_oneand[j]
//            + max_recup_oneand[j][s];
//        }
//
//    }
//    //Affichage de Sum_max_recup_oneand[j]
//    if (DEBUG)
//    {
//        for (int j = 0; j < nb_ands; j++)
//        {
//            cout << "Sum_max_recup_oneand[" << j << "]="
//            << Sum_max_recup_oneand[j] << endl;
//        }
//
//    }
//    //************Fin calcul de Sum_max_recup de chaque AND
//
    
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
    


    
    //calcul des proba de succs de chaque and
    std::vector<long double> proba_and(nb_ands, 1);
    //vecteur qui stocke le max des nombres delements recuperes a partir de chaque stream s
    
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
    sprintf(filename, "MULTIDNFTREE-%s-%d-%d-%.2f", argv[1], nb_ands, nbmaxleaves, ratio);
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
//    long double cost_optimal_singlestream = DBL_MAX;
    long double costeval_andbyand_bycsurp = DBL_MAX;
    long double costeval_andbyand_bycost = DBL_MAX;
//    long double costeval_andbyand_bydecreasingproba = DBL_MAX;
    long double costorderleaves_bycsurq = DBL_MAX;
    long double costorderleaves_bycsurp = DBL_MAX;
    long double costorderleaves_bycost = DBL_MAX;
    long double costorderleaves_bydecreasingproba = DBL_MAX;
    long double costorderleaves_byincreasingproba = DBL_MAX;
    long double costorder_andby_csurp = DBL_MAX;
    long double costorder_andby_cost = DBL_MAX;
    long double costorder_andby_increasingproba = DBL_MAX;
    long double costorder_andby_decreasingproba = DBL_MAX;


    if(with_optimal){
    	//*********************** Calling the exhaustive search for the optimal
    	exhaustive_andbyand(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams,
    	                      cost_optimal);
    	outputfile << seed << "\t"  << "0\t" << cost_optimal << endl;
    }


    if(with_heuristics||with_single_and||only_best_one){
        //***********************Appel de l'heuristique  eval_andbyand_bycsurp:heur1
        costeval_andbyand_bycsurp = 0;
        eval_andbyand_dynamic_by_c_over_p(DNF, nb_ands, nb_leaves_per_and, streamCost, proba_and, nb_streams, costeval_andbyand_bycsurp);
    	outputfile << seed << "\t"  << "20\t" << costeval_andbyand_bycsurp << endl;
    }

    if(with_heuristics)
    {
        //***********************Appel de l'heuristique  eval_andbyand_bycost:heur2
        costeval_andbyand_bycost = 0;
        eval_andbyand_dynamic_bycost(DNF, nb_ands,
                             nb_leaves_per_and, streamCost, proba_and, nb_streams, costeval_andbyand_bycost);
    	outputfile << seed << "\t"  << "21\t" << costeval_andbyand_bycost << endl;
    }
//        //***********************Appel de l'heuristique  eval_andbyand_bydecreasingproba:heur3
//        vector<leaf_place> evaluation_order3;
//        multiset<Feuille> myset_feuille3;
//        std::vector<multiset<Feuille> > disjoint_set3(nb_streams, (myset_feuille3));
//        costeval_andbyand_bydecreasingproba = 0;
//        multiset<int> and_rest3;
//        for (int j = 0; j < nb_ands; j++)
//        {
//            and_rest3.insert(j);
//        }
//        eval_andbyand_bydecreasingproba(DNF, nb_ands,
//                                        nb_leaves_per_and, streamCost, proba_and, nb_streams, costeval_andbyand_bydecreasingproba, and_rest3,
//                                        disjoint_set3, evaluation_order3);
//
//
    if(with_heuristics){
        //***********************Appel de l'heuristique orderleaves_bycsurq:heur4
        vector<leaf_place> evaluation_order4;
        costorderleaves_bycsurq = orderleaves_by_c_over_q(DNF, nb_ands,
                                                    nb_leaves_per_and, nb_streams, streamCost, evaluation_order4);
    	outputfile << seed << "\t"  << "40\t" << costorderleaves_bycsurq << endl;
    }
    if(with_heuristics){
        //***********************Appel de l'heuristique orderleaves_bycsurp:heur5
        vector<leaf_place> evaluation_order5;
        costorderleaves_bycsurp = orderleaves_by_c_over_p(DNF, nb_ands,
                                                    nb_leaves_per_and, nb_streams, streamCost, evaluation_order5);
    	outputfile << seed << "\t"  << "41\t" << costorderleaves_bycsurp << endl;

        //***********************Appel de l'heuristique orderleaves_bycost:heur6
        vector<leaf_place> evaluation_order6;
        costorderleaves_bycost = orderleaves_bycost(DNF, nb_ands,
                                                  nb_leaves_per_and, nb_streams, streamCost, evaluation_order6);
    	outputfile << seed << "\t"  << "42\t" << costorderleaves_bycost << endl;


        //***********************Appel de l'heuristique orderleaves_bydecreasingproba:heur7
        vector<leaf_place> evaluation_order7;
        costorderleaves_bydecreasingproba = orderleaves_bydecreasingproba(DNF, nb_ands,
                                                                        nb_leaves_per_and, nb_streams, streamCost, evaluation_order7);
    	outputfile << seed << "\t"  << "43\t" << costorderleaves_bydecreasingproba << endl;

        //***********************Appel de l'heuristique orderleaves_byincreasingproba:heur8
        vector<leaf_place> evaluation_order8;
        costorderleaves_byincreasingproba = orderleaves_byincreasingproba(DNF, nb_ands,
                                                                        nb_leaves_per_and, nb_streams, streamCost, evaluation_order8);
    	outputfile << seed << "\t"  << "44\t" << costorderleaves_byincreasingproba << endl;

        // Calling heuristic order_leaves_randomly
    	long double cost_random_ordering = order_leaves_randomly(DNF, nb_ands, nb_leaves_per_and, nb_streams, streamCost);
    	outputfile << seed << "\t"  << "45\t" << cost_random_ordering << endl;

//    	// Calling the heuristic taken from the paper by Lipyeow
//    	long double cost_by_lipyeow_decreasing = Lipyeow_ordering(DNF, nb_ands, nb_leaves_per_and, streamCost, nb_streams, true);
//    	outputfile << seed << "\t"  << "46\t" << cost_by_lipyeow_decreasing << endl;
//    	long double cost_by_lipyeow_increasing = Lipyeow_ordering(DNF, nb_ands, nb_leaves_per_and, streamCost, nb_streams, false);
//    	outputfile << seed << "\t"  << "47\t" << cost_by_lipyeow_increasing << endl;

        //***********************Appel de l'heuristique order_andby_csurp:heur9
        costorder_andby_csurp = 0;
        multiset<int> and_rest9;
        for (int j = 0; j < nb_ands; j++)
        {
            and_rest9.insert(j);
        }
        vector<leaf_place> evaluation_order9;
        multiset<ratio_and> and_final_order9;
        vector<leaf_place> initleaf_place9;
        vector<vector<leaf_place> > leaf_order9(nb_ands, (initleaf_place9));
        multiset<Feuille> myset_feuille9;
        std::vector<multiset<Feuille> >
        disjoint_set9(nb_streams, (myset_feuille9));

        order_andby_csurp(DNF, nb_ands,
                          nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andby_csurp ,
                          and_rest9, and_final_order9, leaf_order9, disjoint_set9,
                          evaluation_order9);
    	outputfile << seed << "\t"  << "30\t" << costorder_andby_csurp << endl;

        //***********************Appel de l'heuristique order_andby_cost:heur10
        costorder_andby_cost = 0;
        multiset<int> and_rest10;
        for (int j = 0; j < nb_ands; j++)
        {
            and_rest10.insert(j);
        }
        vector<leaf_place> evaluation_order10;
        multiset<ratio_and> and_final_order10;
        vector<leaf_place> initleaf_place10;
        vector<vector<leaf_place> > leaf_order10(nb_ands, (initleaf_place10));
        multiset<Feuille> myset_feuille10;
        std::vector<multiset<Feuille> >
        disjoint_set10(nb_streams, (myset_feuille10));

        order_andby_cost(DNF, nb_ands,
                         nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andby_cost,
                         and_rest10, and_final_order10, leaf_order10, disjoint_set10,
                         evaluation_order10);
    	outputfile << seed << "\t"  << "31\t" << costorder_andby_cost << endl;

        //***********************Appel de l'heuristique order_andby_increasingproba:heur11
        costorder_andby_increasingproba = 0;
        multiset<int> and_rest11;
        for (int j = 0; j < nb_ands; j++)
        {
            and_rest11.insert(j);
        }
        vector<leaf_place> evaluation_order11;
        multiset<ratio_and> and_final_order11;
        vector<leaf_place> initleaf_place11;
        vector<vector<leaf_place> > leaf_order11(nb_ands, (initleaf_place11));
        multiset<Feuille> myset_feuille11;
        std::vector<multiset<Feuille> >
        disjoint_set11(nb_streams, (myset_feuille11));

        order_andby_increasingproba(DNF, nb_ands,
                                    nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andby_increasingproba,
                                    and_rest11, and_final_order11, leaf_order11, disjoint_set11,
                                    evaluation_order11);
    	outputfile << seed << "\t"  << "32\t" << costorder_andby_increasingproba << endl;

        //***********************Appel de l'heuristique order_andby_decreasingproba:heur12
        costorder_andby_decreasingproba = 0;
        multiset<int> and_rest12;
        for (int j = 0; j < nb_ands; j++)
        {
            and_rest12.insert(j);
        }
        vector<leaf_place> evaluation_order12;
        multiset<ratio_and> and_final_order12;
        vector<leaf_place> initleaf_place12;
        vector<vector<leaf_place> > leaf_order12(nb_ands, (initleaf_place12));
        multiset<Feuille> myset_feuille12;
        std::vector<multiset<Feuille> >
        disjoint_set12(nb_streams, (myset_feuille12));

        order_andby_decreasingproba(DNF, nb_ands,
                                    nb_leaves_per_and, streamCost, proba_and, nb_streams, costorder_andby_decreasingproba,
                                    and_rest12, and_final_order12, leaf_order12, disjoint_set12,
                                    evaluation_order12);
    	outputfile << seed << "\t"  << "33\t" << costorder_andby_decreasingproba << endl;

    }//fin if Heuristiques

    long double cost_progdyn = -1;
    if(with_progdyn){
        //***********************Appel de l'heuristique prog_dyn:heur0
        if(int_overflow_for_progdyn){
        	outputfile << "#INT OVERFLOW  for progdyn" << endl;
        }
        else{
        	long double progdyn = -1;
        	std::vector<int> best_stream_order;

        	int data_element_size = sizeof(bool) + sizeof(long double) + sizeof(int) + nb_streams*sizeof(int);
        	if (MYDEBUG) cout << "Memory allocation of " << nb_cases << " elements of size " << data_element_size << endl;
        	if (MYDEBUG) cout << "Equivalent to " << nb_cases*1.0*data_element_size/1073741824.0 << " GB" << endl;
        	// cout << "Right before allocating marqueurs" << endl;
        	std::vector<case_elem> marqueurs(nb_cases, init);
        	// cout << "Right after allocating marqueurs" << endl;

        	// Call to the function doing the work
        	if (MYDEBUG) cout << "CALL to the dynamic programming algorithm." << endl;
        	progdyn = prog_dyn_DNF(0, DNF, nb_streams, streamCost, nb_ands, nb_leaves_per_and,
        			marqueurs, vector_max, nb_cases, best_stream_order);
        	if (MYDEBUG) cout << "AFTER the call to the dynamic programming algorithm." << endl;
        	if(DEBUG2)
        	{
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
    	for (int i = 0; i < nb_leaves_per_and[j]; i++){
    		delete [] DNF[j][i].nb_data_recup;
    	}
    	delete [] DNF[j];
    	//delete [] max_recup_oneand[j];
    }
    delete [] DNF;
    delete [] streamCost;
    delete [] nb_leaves_per_and;
    delete [] filename;
    //delete [] max_recup_oneand;
}

int
main(int argc, char ** argv)
{
    argument_processing_for_DNF(argc, argv);
}

