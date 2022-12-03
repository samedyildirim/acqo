/*
 * acqo.h
 *
 *  Created on: Dec 21, 2018
 *      Author: samed
 */

#ifndef ACQO_H_
#define ACQO_H_

typedef struct Ant {
	int * path;
	double cost;
} Ant;

typedef struct Pheromone {
	double * pheromone_matrix;
	double ph_max;
	double ph_min;
	double ph_init;
	double base_cost;
} Pheromone;

typedef struct JoinedRel {
	RelOptInfo *jr;
	int number_of_rel;
} JoinedRel;

typedef struct CostCacheSearchTree {
	List* path_list;
} CostCacheSearchTree;

#endif /* ACQO_H_ */
