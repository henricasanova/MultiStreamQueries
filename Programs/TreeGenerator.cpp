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


#include <stdio.h>
#include <stdlib.h>
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
#include "DNFScheduling.hpp"

#include <boost/assign/list_of.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include "boost/tuple/tuple.hpp"
#include "boost/tuple/tuple_comparison.hpp"
#include <boost/math/distributions/uniform.hpp>
#include <boost/random.hpp>
#include <boost/random/mersenne_twister.hpp>
using namespace std;



void
argument_processing(int argc, char ** argv)
{
	// Reading the parameters
	char * structure = argv[1];

	int nband =boost::lexical_cast<int>(argv[3]);
	int nbleafs=boost::lexical_cast<int>(argv[5]);
	double reuse= boost::lexical_cast<double>(argv[7]);
	int nb_streams = ceil(nband*nbleafs/reuse);
	int base_seed = boost::lexical_cast<int>(argv[9]);
	int nb_seeds = boost::lexical_cast<int>(argv[11]);
	int heuristics = boost::lexical_cast<int>(argv[13]);
	int localrun = boost::lexical_cast<int>(argv[15]);

	// Creation of the output file
    ofstream script;
    char * generated_trees = new char [2048];
    sprintf(generated_trees, "generated_trees-%s-%d-%d-%.2f-%d-%d-%d-%d.sh", structure, nband, nbleafs, reuse, base_seed, nb_seeds, heuristics, localrun);

    script.open(generated_trees, ios::out);
    if (!(script.is_open()))
    {
        cout << "ERROR opening file: " << generated_trees << endl;
        abort();
    }

    script << "#!/bin/bash" << endl;
    // Copy the arguments of the program call
     script << "# ARGUMENTS\t";
     for(int i=1; i<argc; i++){
       script << argv[i] << " ";
     }
     script << endl;

     if(localrun){
    	 script << "topdirectory=\"./\";"<<endl;
     }
     else{
    	 script << "topdirectory=\"/warehouse/fvivien/Aloha/Programs/\";"<<endl;
     }


if(strcmp(structure,"FIXE")==0){
     
       for (int seed = base_seed; seed < base_seed+nb_seeds  ; seed++){


            int stream;
            int nbrecup;
            long double proba;

            if (localrun){
            	script << " `$topdirectory/DNFScheduling ";
            }
            else{
            	script << "qsub -q \"2Gmax $topdirectory/launch_script.sh ";
            }
            		script << structure << " RATIO " << reuse << " TREE "<< seed ;
            script << " NBSTREAMS " << nb_streams <<" NBAND "<< nband << " NBMAXLEAVES " << nbleafs << " NBLEAF " ;

        for (int j = 0; j <nband; j++){
                script << nbleafs<<" ";
                }

            boost::mt19937 rng;
            boost::uniform_01<> unif;
            // Initialization of the random generator with the seed
            rng.seed(seed);
            boost::variate_generator<boost::mt19937, boost::uniform_01<> > die(rng, unif);


          script << "VALUE";
          // Loop on all the leaves of all the ANDs
          for (int j = 0; j <nband  ; j++){
                for (int i = 0; i < nbleafs; i++){

                	// Stream the leaf depends upon
                	long double quantile2 = die();
                    stream = floor(nb_streams*quantile2);
                    if(stream==nb_streams){
                    	stream = nb_streams-1;
                    }

                    // Number of data elements needed
                    long double quantile3 = die();
                    nbrecup = floor(1 + 5*quantile3);
                    if (nbrecup==6){
                    	nbrecup = 5;
                    }

                    // Proba of success
                    long double quantile4 = die();
                    proba = quantile4;

                    script <<" "<<stream<<" "<< nbrecup<<" "<< proba;
                }
            }

            // Definition of the costs of the streams
            script << " STREAMCOST";
            for(int stream_id=0; stream_id<nb_streams; stream_id++){
                long double quantile5 = die();
                long double cost = 1+9*quantile5;
                script << " " << cost;
            }
            script << " HEUR " << heuristics;
            if (localrun){
            	script << "`;"<< endl;
            }
            else{
            	script << "\";"<< endl;
            }
        }
 }
else if(strcmp(structure,"VAR")==0){
	// Array to store the number of leaves of each AND

	           int * nbleafsand = new int[nband];

	       for (int seed = base_seed; seed < base_seed+nb_seeds  ; seed++){


	            int stream;
	            int nbrecup;
	            long double proba;

	            if (localrun){
	            	script << "echo \"seed = "  << seed << "\""<< endl;
	            	script << "`$topdirectory/DNFScheduling ";
	            }
	            else{
	            	script << "qsub -q test \"$topdirectory/launch_script.sh ";
	            }
	            script << structure << " RATIO " << reuse << "  TREE "<<seed;
	         script << " NBSTREAMS " << nb_streams <<" NBAND "<< nband << " NBMAXLEAVES " << nbleafs << " NBLEAF " ;


	            boost::mt19937 rng;
	            boost::uniform_01<> unif;
	            // Initialization of the random generator with the seed
	            rng.seed(seed);
	            boost::variate_generator<boost::mt19937, boost::uniform_01<> > die(rng, unif);

	            for (int j = 0; j <nband; j++){
                    long double quantile1 = die();
                    nbleafsand[j] = floor(1+nbleafs*quantile1);
                    if(nbleafsand[j]==1+nbleafs){
                    	nbleafsand[j] = nbleafs;
                    }
                    script << nbleafsand[j]<<" ";
	            }

	          script << "VALUE";
	          // Loop on all the leaves of all the ANDs
	          for (int j = 0; j <nband  ; j++){
	                for (int i = 0; i < nbleafsand[j]; i++){
	                	// Stream the leaf depends upon
	                    long double quantile2 = die();
	                    stream = floor(nb_streams*quantile2);
	                    if(stream==nb_streams){
	                    	stream = nb_streams-1;
	                    }
	                    // Number of data elements needed
	                    long double quantile3 = die();
	                    nbrecup = floor(1 + 5*quantile3);
	                    if (nbrecup==6){
	                    	nbrecup = 5;
	                    }

	                    // Proba of success
	                    long double quantile4 = die();
	                    proba = quantile4;


	                    script <<" "<<stream<<" "<< nbrecup<<" "<< proba;
	                }
	            }

	            // Definition of the costs of the streams
	            script << " STREAMCOST";
	            for(int stream_id=0; stream_id<nb_streams; stream_id++){
	                long double quantile5 = die();
	                long double cost = 1+9*quantile5;
	                script << " " << cost;
	            }
	            script << " HEUR " << heuristics;
	            if (localrun){
	            	script << "`;"<< endl;
	            }
	            else{
	            	script << "\";"<< endl;
	            }
	        }
	 }
}



int
main(int argc, char ** argv)
{
    argument_processing(argc, argv);
}
