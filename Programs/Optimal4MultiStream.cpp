/*
 * Optimal.cpp
 *
 *  Created on: 25 juin 2013
 *      Author: fvivien
 */

#include <iostream>
#include <algorithm>
#include "MultiStream.hpp"

using namespace std;

int fact(int n){
	int facto = 1;
	for(int i=2; i<=n; i++){
		facto *= i;
	}
	return facto;
}

void allPermutations4And(int n, int * factorial, int *** permutations){
	int facto = fact(n);
	(*factorial) = facto;
	(*permutations) = new int * [facto];
	for(int i=0; i<facto; i++){
		(*permutations)[i] = new int[n];
	}
	int * base = new int [n];
	for(int i=0; i<n; i++){
		base[i] = i;
	}

	int permutation_rank = 0;
	do {
		for(int i=0; i<n; i++){
			(*permutations)[permutation_rank][i] = base[i];
		}
		permutation_rank++;
	  } while (std::next_permutation(base,base+n) );

	delete [] base;
}

void allPermutations4DNF(int nb_and, int * nb_leafs_per_and, int * nb_and_permutations, int *** and_permutations, int * factorials, int *** all_permutations){
	allPermutations4And(nb_and, nb_and_permutations, and_permutations);
	for(int i=0; i<nb_and; i++){
		allPermutations4And(nb_leafs_per_and[i], &(factorials[i]), &(all_permutations[i]));
	}
}


void enumerate_permutations(long double &cost, int nb_total_leaves, int Order_NbLeavesSet,
		int * Order_AndIds, int * Order_LeafIds,
		leaf ** DNFTree, int nb_and, int * nb_leavesperAND, int nb_streams, long double * streamCost,
		int * and_permutation,
		int and_rank, int * nb_permutations, int *** all_the_permutations){
	int and_id = and_permutation[and_rank];
	// Whatever the permutation, all the leaves added to the built order correspond to the same AND
	for(int i=0; i<nb_leavesperAND[and_id]; i++){
		Order_AndIds[Order_NbLeavesSet+i] = and_id;
	}
	if(and_rank == nb_and-1){
		assert(nb_total_leaves == Order_NbLeavesSet+nb_leavesperAND[and_id]);
	}
	// We traverse all the permutations for that AND
	for(int permut_rank=0; permut_rank<nb_permutations[and_id]; permut_rank++){
		if (and_rank==0){ cout << " " << 1+permut_rank << flush;}
		// For a permutation, we copy the leaf IDs in the order array
		for(int leaf_rank=0; leaf_rank<nb_leavesperAND[and_id]; leaf_rank++){
			Order_LeafIds[Order_NbLeavesSet+leaf_rank] = all_the_permutations[and_id][permut_rank][leaf_rank];
		}
		// If the test is true, we are considering the last of the ANDs, and we call the evaluation function
		if(and_rank == nb_and-1){
//			time_t start_time = time (NULL);
			long double order_cost = Cost4Arrays(DNFTree, nb_and, nb_leavesperAND, nb_streams, streamCost,
					nb_total_leaves, Order_AndIds, Order_LeafIds);
//			time_t middle_time = time (NULL);
//			long double order_cost_new = Cost4Arrays_optimized(DNFTree, nb_and, nb_leavesperAND, streamCost,
//					nb_total_leaves, Order_AndIds, Order_LeafIds);
//			time_t end_time = time (NULL);
//			if (abs(order_cost-order_cost_new) > 0.0000001){
//				cout << "There should be a bug somewhere the two costs being " << order_cost << " and " << order_cost_new << endl;
//				abort();
//			}
//			int original_time = difftime(middle_time, start_time);
//			int optimized_time = difftime(end_time, middle_time);

//			cout  << 100*(original_time-optimized_time)/original_time << "\t"<< original_time << "\t" << optimized_time << endl;

			if (order_cost<cost){
				cost = order_cost;
			}
		}
		else{
			enumerate_permutations(cost, nb_total_leaves,
					Order_NbLeavesSet+nb_leavesperAND[and_id], Order_AndIds, Order_LeafIds,
					DNFTree, nb_and, nb_leavesperAND, nb_streams, streamCost,
					and_permutation,and_rank+1, nb_permutations, all_the_permutations);
		}
	}
}

void enumerate_permutations_optim(long double &optimalcost, long double partialcost, int nb_total_leaves, int Order_NbLeavesSet,
		int * Order_AndIds, int * Order_LeafIds,
		leaf ** DNFTree, int nb_and, int * nb_leavesperAND, long double * streamCost,
		int * and_permutation,
		int and_rank, int * nb_permutations, int *** all_the_permutations,
		int nb_streams, int * max_element_per_stream, bool *** AND_needs_data, long double *** proba_data_read,
		long double * probaAndTrue, bool * andCompleted){
	int and_id = and_permutation[and_rank];
	// Whatever the permutation, all the leaves added to the built order correspond to the same AND
	for(int i=0; i<nb_leavesperAND[and_id]; i++){
		Order_AndIds[Order_NbLeavesSet+i] = and_id;
	}
	int rank_first_leaf = Order_NbLeavesSet;
	int rank_last_leaf = rank_first_leaf+nb_leavesperAND[and_id];

	if(and_rank == nb_and-1){
		assert(nb_total_leaves == Order_NbLeavesSet+nb_leavesperAND[and_id]);
	}
	// We traverse all the permutations for that AND
	for(int permut_rank=0; permut_rank<nb_permutations[and_id]; permut_rank++){
		if (WITHPROGRESS){ if (and_rank==0){ cout << " " << 1+permut_rank << flush;}}
		// For a permutation, we copy the leaf IDs in the order array
		for(int leaf_rank=0; leaf_rank<nb_leavesperAND[and_id]; leaf_rank++){
			Order_LeafIds[Order_NbLeavesSet+leaf_rank] = all_the_permutations[and_id][permut_rank][leaf_rank];
		}
		// If the test is true, we are considering the last of the ANDs, and we call the evaluation function
		long double order_cost = DBL_MAX;
		clock_t clock_start = clock();
		if (INDEBUG){
			if(and_rank == nb_and-1){
				order_cost = Cost4Arrays(DNFTree, nb_and, nb_leavesperAND, nb_streams, streamCost,
						nb_total_leaves, Order_AndIds, Order_LeafIds);
			}
		}
		clock_t clock_middle = clock();

		long double order_cost_new = Cost4Arrays_stripped(DNFTree, nb_and, nb_leavesperAND, streamCost,
				nb_total_leaves, rank_first_leaf, rank_last_leaf, Order_AndIds, Order_LeafIds, nb_streams, max_element_per_stream,
				AND_needs_data, proba_data_read, probaAndTrue, andCompleted);
		clock_t clock_end = clock();
		long double newpartialcost = partialcost+order_cost_new;
		if(and_rank == nb_and-1){
			if (INDEBUG){
				if (abs(order_cost-newpartialcost) > 0.0000001){
					cout << "There should be a bug somewhere the two costs being " << order_cost << " and " << newpartialcost << endl;
					abort();
				}
				int new_time = clock_end-clock_middle;
				int old_time = clock_middle-clock_start;
				if (PRINTSTATS) cout  << 100*(new_time-old_time)/(old_time) << "%\t"<< (new_time) << "\t" << (old_time) << endl;
			}
			if (newpartialcost<optimalcost){
				optimalcost = newpartialcost;
//				if(DEBUGMULTIGREEDY){
//					for(int leaf_rank=0; leaf_rank<nb_leavesperAND[and_id]; leaf_rank++){
//						cout << all_the_permutations[and_id][permut_rank][leaf_rank] << " ";
//					}
//					cout << endl;
//				}
//				cout << optimalcost << "\t";
//				for(int i=0; i<nb_total_leaves; i++){
//					cout << "(" << Order_AndIds[i] << ", " << Order_LeafIds[i] << ")  ";
//				}
//				cout << endl;
			}
//			cout << optimalcost << "\t" << newpartialcost << "\t";
//			for(int i=0; i<nb_total_leaves; i++){
//				cout << "(" << Order_AndIds[i] << ", " << Order_LeafIds[i] << ")  ";
//			}
//			cout << endl;
		}
		else{
			andCompleted[and_id] = true;
			enumerate_permutations_optim(optimalcost, newpartialcost, nb_total_leaves,
					Order_NbLeavesSet+nb_leavesperAND[and_id], Order_AndIds, Order_LeafIds,
					DNFTree, nb_and, nb_leavesperAND, streamCost,
					and_permutation,and_rank+1, nb_permutations, all_the_permutations, nb_streams, max_element_per_stream,
					AND_needs_data, proba_data_read, probaAndTrue, andCompleted);
			andCompleted[and_id] = false;
		}
		// The next permutation is another permutation of the same AND
		// Therefore, we erase what was set for that permutation
		for(int leaf_id=0; leaf_id<nb_leavesperAND[and_id]; leaf_id++){
			for(int stream_id=0; stream_id<nb_streams; stream_id++){
				int nb_data_recup = DNFTree[and_id][leaf_id].nb_data_recup[stream_id];
				for(int element=0; element < nb_data_recup; element++){
					//			for(int stream_id=0; stream_id<nb_streams; stream_id++){
					//				for(int nb_stream_elements=0; nb_stream_elements < max_elements_per_stream[stream_id]; nb_stream_elements++){
					AND_needs_data[and_id][stream_id][element] = false;
				}
			}
		}
	}
}


void
exhaustive_andbyand(leaf ** DNFTree, int nb_and, int * nb_leavesperAND,
                      long double * streamCost, vector<long double> proba_and, int nb_streams,
                      long double & optimal_cost)
{
	int nb_and_permutation = -1;
	int ** permutations_of_ANDs;
	int * nb_permutations_per_and = new int[nb_and];
	int *** all_the_permutations = new int ** [nb_and];
	// Building all elementary permutations
	allPermutations4DNF(nb_and, nb_leavesperAND, &nb_and_permutation, &permutations_of_ANDs, nb_permutations_per_and, all_the_permutations);

	// Data structure to store the order to be evaluated
	int nb_leaves_in_DNF = 0;
	for(int i=0; i<nb_and; i++){
		nb_leaves_in_DNF += nb_leavesperAND[i];
	}
	int * Order_AndIds = new int [nb_leaves_in_DNF];
	int * Order_LeafIds = new int [nb_leaves_in_DNF];

	// Data structure to record the maximum number of elements per stream
	int * max_elements_per_stream = new int [nb_streams];
	for(int stream_id=0; stream_id<nb_streams; stream_id++){
		max_elements_per_stream[stream_id] = 0;
	}
	for(int AND_rank = 0; AND_rank < nb_and; AND_rank++){
		for(int leaf_rank=0; leaf_rank < nb_leavesperAND[AND_rank]; leaf_rank++){
			for(int stream=0; stream<nb_streams; stream++){
				if(max_elements_per_stream[stream] < DNFTree[AND_rank][leaf_rank].nb_data_recup[stream]){
					max_elements_per_stream[stream] = DNFTree[AND_rank][leaf_rank].nb_data_recup[stream];
				}
			}
		}
	}
	// Data structure to record whether any input data item has already been encountered in preceding leaves
    bool * andCompleted = new bool[nb_and];
	bool *** AND_needs_data = new bool ** [nb_and];
	long double *** proba_data_read = new long double ** [nb_and];
	for(int AND_rank = 0; AND_rank < nb_and; AND_rank++){
		andCompleted[AND_rank] = false;
		AND_needs_data[AND_rank] = new bool * [nb_streams];
		proba_data_read[AND_rank] = new long double * [nb_streams];
		for(int stream_id=0; stream_id<nb_streams; stream_id++){
			AND_needs_data[AND_rank][stream_id] = new bool [max_elements_per_stream[stream_id]];
			proba_data_read[AND_rank][stream_id] = new long double [max_elements_per_stream[stream_id]];
			for(int nb_stream_elements=0; nb_stream_elements < max_elements_per_stream[stream_id]; nb_stream_elements++){
				AND_needs_data[AND_rank][stream_id][nb_stream_elements] = false;
				proba_data_read[AND_rank][stream_id][nb_stream_elements] = 0;
			}
		}
	}
	// Computation of the probability of each AND to evaluate to true
	long double * probaAndTrue = new long double[nb_and];
	for(int AND_rank = 0; AND_rank < nb_and; AND_rank++){
		probaAndTrue[AND_rank] = 1;
		for(int leaf_rank=0; leaf_rank < nb_leavesperAND[AND_rank]; leaf_rank++){
			probaAndTrue[AND_rank] *= DNFTree[AND_rank][leaf_rank].proba;
		}
	}
	optimal_cost = DBL_MAX;

	for(int i=0; i<nb_and_permutation; i++){
		if (WITHPROGRESS)
		{
			cout << endl << i+1 << "/" << nb_and_permutation << ":\t";
		}
		enumerate_permutations_optim(optimal_cost, 0, nb_leaves_in_DNF, 0, Order_AndIds, Order_LeafIds,
				DNFTree, nb_and, nb_leavesperAND, streamCost, permutations_of_ANDs[i],
				0, nb_permutations_per_and, all_the_permutations, nb_streams, max_elements_per_stream,
				AND_needs_data, proba_data_read, probaAndTrue, andCompleted);
	}

	// De-allocation
	for(int i=0; i<nb_and; i++){
		for(int j=0; j<nb_permutations_per_and[i]; j++){
			delete [] all_the_permutations[i][j];
		}
		delete [] all_the_permutations[i];
		delete [] permutations_of_ANDs[i];
	}
	for(int i=0; i<nb_and; i++){
		for(int j=0; j<nb_streams; j++){
			delete [] AND_needs_data[i][j];
			delete [] proba_data_read[i][j];
		}
		delete [] AND_needs_data[i];
		delete [] proba_data_read[i];
	}
	delete [] max_elements_per_stream;
	delete [] AND_needs_data;
	delete [] proba_data_read;
	delete [] probaAndTrue;
	delete [] andCompleted;
	delete [] permutations_of_ANDs;
	delete [] all_the_permutations;
	delete [] nb_permutations_per_and;
	delete [] Order_LeafIds;
	delete [] Order_AndIds;
}

// First version developped
void
exhaustive_andbyand_original(leaf ** DNFTree, int nb_and, int * nb_leavesperAND,
                      long double * streamCost, vector<long double> proba_and, int nb_streams,
                      long double & optimal_cost)
{
	int nb_and_permutation = -1;
	int ** permutations_of_ANDs;
	int * nb_permutations_per_and = new int[nb_and];
	int *** all_the_permutations = new int ** [nb_and];
	// Building all elementary permutations
	allPermutations4DNF(nb_and, nb_leavesperAND, &nb_and_permutation, &permutations_of_ANDs, nb_permutations_per_and, all_the_permutations);

	// Data structure to syore the order to be evaluated
	int nb_leaves_in_DNF = 0;
	for(int i=0; i<nb_and; i++){
		nb_leaves_in_DNF += nb_leavesperAND[i];
	}
	int * Order_AndIds = new int [nb_leaves_in_DNF];
	int * Order_LeafIds = new int [nb_leaves_in_DNF];

	optimal_cost = DBL_MAX;

	for(int i=0; i<nb_and_permutation; i++){
		cout << endl << i+1 << "/" << nb_and_permutation << ":\t";
		enumerate_permutations(optimal_cost, nb_leaves_in_DNF, 0, Order_AndIds, Order_LeafIds,
				DNFTree, nb_and, nb_leavesperAND, nb_streams, streamCost, permutations_of_ANDs[i],
				0, nb_permutations_per_and, all_the_permutations);
//		enumerate_permutations(optimal_cost, nb_leaves_in_DNF, 0, Order_AndIds, Order_LeafIds,
//				DNFTree, nb_and, nb_leavesperAND, streamCost, permutations_of_ANDs[i],
//				0, nb_permutations_per_and, all_the_permutations);
	}

	// De-allocation
	for(int i=0; i<nb_and; i++){
		for(int j=0; j<nb_permutations_per_and[i]; j++){
			delete [] all_the_permutations[i][j];
		}
		delete [] all_the_permutations[i];
		delete [] permutations_of_ANDs[i];
	}
	delete [] permutations_of_ANDs;
	delete [] all_the_permutations;
	delete [] nb_permutations_per_and;
	delete [] Order_LeafIds;
	delete [] Order_AndIds;
}

