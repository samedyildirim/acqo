/*
 * acqo.c
 *
 *  Created on: Dec 21, 2018
 *      Author: samed
 */

#include "postgres.h"
#include "fmgr.h"
#include <math.h>

#include "optimizer/planner.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/joininfo.h"
#include "utils/guc.h"
#include "nodes/pg_list.h"
#include "acqo.h"
#include "optimizer/geqo.h"
#include "utils/memutils.h"

#include <string.h>

PG_MODULE_MAGIC;

join_search_hook_type prev_join_search_hook = NULL;
static int acqo_ant_count = 0;
static bool acqo_enable = true;
static unsigned short seed[3];

static double acqo_alfa = 1;
static double acqo_beta = 0;
static double acqo_evaporation_level = 0.02;
static int acqo_round_count = 50;
static bool acqo_print_pheromone = false;
static bool acqo_print_debug = false;
static bool acqo_force_geqo = false;
static double acqo_seed = 0;

void 		_PG_init(void);
void 		_PG_fini(void);
static bool desirable_join(PlannerInfo *, RelOptInfo *, RelOptInfo *);
static void load_params();

static void 		acqo_multiply_pheromone_to_all(Pheromone *,int ,double );
static void 		acqo_calculate_ant_paths_costs(PlannerInfo *, int , List *,Ant *,int );
static double 		acqo_calculate_single_ant_path_cost(PlannerInfo *, int , List *,Ant *);
static void 		acqo_create_path(PlannerInfo *, List *, Pheromone* ,Ant* , int );
static void 		acqo_create_paths(PlannerInfo *, List *, Pheromone* ,Ant* , int ,int );
static void 		acqo_create_random_path(Ant *,int, PlannerInfo *, int , List *);
static void 		acqo_deposit_pheromone(Pheromone *,Ant* ,int );
static void 		acqo_evaporate_pheromones(Pheromone *,int );
static double 		acqo_get_pheromone(Pheromone *,int , int , int );
static RelOptInfo*	acqo_get_result(PlannerInfo *, int , List *,Ant *);
//static RelOptInfo*	acqo_get_result2(PlannerInfo *, int , List *,Ant *);
static Ant* 		acqo_init_ants(int ,int );
static Pheromone* 	acqo_init_nn_pheromone_matrix (int );
static void 		acqo_init_pheromone(Pheromone *,int );
static RelOptInfo*	acqo_join_planner(PlannerInfo *, int , List *);
static void 		acqo_local_search_2opt(Ant*, PlannerInfo *,int , List*);
static List* 		acqo_merge_rels(List* , PlannerInfo *, JoinedRel* , int , bool );
void 				acqo_path_copy(int* , int* , int );
static int 			acqo_select_best_ant(Ant* ,int );
static void 		acqo_select_next_node(PlannerInfo *, List *, Pheromone* ,Ant *,int , short *, int );
static void 		acqo_set_min_max_pheromone(Pheromone *, double , int );
static void 		acqo_set_min_pheromone(Pheromone *,PlannerInfo *, int , List *);
static void 		acqo_set_pheromone(Pheromone *,int , int , int , double );
static void 		acqo_update_pheromones(Pheromone *,Ant* ,int );


static double acqo_check_cost_cache(Ant *,int );
static void acqo_add_cost_cache(Ant *,int );

/* Zaman ölçümlemesi için eklenen geçici bölüme */
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>

typedef enum type_timer {REAL, VIRTUAL} TIMER_TYPE;

static void start_timers(void);
static double elapsed_time(TIMER_TYPE type);

static struct rusage res;
static struct timeval tp;
static double virtual_time, real_time;

static void start_timers(void)
/*
      FUNCTION:       virtual and real time of day are computed and stored to
                      allow at later time the computation of the elapsed time
		      (virtual or real)
      INPUT:          none
      OUTPUT:         none
      (SIDE)EFFECTS:  virtual and real time are computed
*/
{
    getrusage( RUSAGE_SELF, &res );
    virtual_time = (double) res.ru_utime.tv_sec +
		   (double) res.ru_stime.tv_sec +
		   (double) res.ru_utime.tv_usec / 1000000.0 +
		   (double) res.ru_stime.tv_usec / 1000000.0;

    gettimeofday( &tp, NULL );
    real_time =    (double) tp.tv_sec +
		   (double) tp.tv_usec / 1000000.0;
}



static double elapsed_time(TIMER_TYPE type)
/*
      FUNCTION:       return the time used in seconds (virtual or real, depending on type)
      INPUT:          TIMER_TYPE (virtual or real time)
      OUTPUT:         seconds since last call to start_timers (virtual or real)
      (SIDE)EFFECTS:  none
*/
{
    if (type == REAL) {
        gettimeofday( &tp, NULL );
        return( (double) tp.tv_sec +
		(double) tp.tv_usec / 1000000.0
		- real_time );
    }
    else {
        getrusage( RUSAGE_SELF, &res );
        return( (double) res.ru_utime.tv_sec +
		(double) res.ru_stime.tv_sec +
		(double) res.ru_utime.tv_usec / 1000000.0 +
		(double) res.ru_stime.tv_usec / 1000000.0
		- virtual_time );
    }

}
/* Geçici bölüm sonu */

static Pheromone * acqo_init_nn_pheromone_matrix (int node_count){
	Pheromone *pheromone;
	//int i,j;

	pheromone = (Pheromone*) palloc(sizeof(Pheromone));
	pheromone->pheromone_matrix = (double*) palloc(node_count * node_count * sizeof(double));
	pheromone->ph_init = 0;
	pheromone->ph_max  = 0;
	pheromone->ph_min  = 0;
	pheromone->base_cost = 0;
/*
	for(i=0;i<node_count;i++)
		for(j=0;j<node_count;j++)
			acqo_set_pheromone(pheromone,node_count,i,j,0.0);*/

	return pheromone;
}

void acqo_path_copy(int* destination, int* source, int count){
	int i;
	for(i=0;i<count;i++)
		destination[i] = source[i];
}

static void acqo_local_search_2opt(Ant *ant, PlannerInfo * root,int levels_needed, List *initial_rels){
	int n1,n2;
	int i;
	int improvement=1;
	double old_cost;
	Ant *new_ants;

	new_ants = acqo_init_ants(2,levels_needed);

	acqo_path_copy(new_ants[0].path,ant->path,levels_needed);
	new_ants[0].cost = ant->cost;

	while(improvement==1){
		improvement=0;
		n1=pg_erand48(seed)*(levels_needed-2);
		n2=pg_erand48(seed)*(levels_needed-1-n1)+n1;

		acqo_path_copy(new_ants[1].path,new_ants[0].path,n1);
		for(i=0;i<n2-n1+1;i++){
			new_ants[1].path[n1+i] = new_ants[0].path[n2-i];
		}

		acqo_path_copy(new_ants[1].path+n2+1,new_ants[0].path+n2+1,levels_needed-n2-1);
		new_ants[1].cost = acqo_calculate_single_ant_path_cost(root,levels_needed,initial_rels,&(new_ants[1]));
		if(new_ants[1].cost != -1 && new_ants[0].cost > new_ants[1].cost){
			improvement = 1;
			new_ants[0].cost = new_ants[1].cost;
			acqo_path_copy(new_ants[0].path,new_ants[1].path,levels_needed);
		}
	}

	if(ant->cost > new_ants[0].cost){
		//elog(LOG,"acqo: local search öncesi cost: %f, sonrası cost: %f",ant->cost , new_ants[0].cost);
		acqo_path_copy(ant->path,new_ants[0].path,levels_needed);
		ant->cost = new_ants[0].cost;
	}
	pfree((void*)new_ants[0].path);
	pfree((void*)new_ants[1].path);
	pfree((void*)new_ants);
}

static void acqo_set_min_max_pheromone(Pheromone *pheromone, double cost, int node_count){
	pheromone->base_cost = cost;
	pheromone->ph_max = 1.0/(cost*acqo_evaporation_level);
	pheromone->ph_min = pheromone->ph_max/(2.0*node_count);
	pheromone->ph_init = pheromone->ph_min;
	//elog(LOG,"acqo: cost: %f, ph_max: %.15f, ph_min: %.15f",cost,pheromone->ph_max,pheromone->ph_min);
}

static Ant* acqo_init_ants(int ant_count,int node_count){
	Ant* ants;
	int i;

	ants = (Ant*) palloc(ant_count * sizeof(Ant));

	for(i=0;i<ant_count;i++){
		ants[i].cost = -1;
		ants[i].path = (int*)palloc(node_count * sizeof(int));
	}

	return ants;
}

static void acqo_set_pheromone(Pheromone *pheromone,int node_count, int node_1, int node_2, double value){
	*(pheromone->pheromone_matrix + node_1*node_count + node_2) = value;
}

static double acqo_get_pheromone(Pheromone *pheromone,int node_count, int node_1, int node_2){
	return *(pheromone->pheromone_matrix + node_1*node_count + node_2);
}

static void acqo_set_min_pheromone(Pheromone *pheromone,PlannerInfo *root, int levels_needed, List *initial_rels){
	Ant *ants;
	int ant_count=1;
	int best_random_ant;
	int i;
	ants = acqo_init_ants(ant_count,levels_needed);

	for(i=0;i<ant_count;i++){
		acqo_create_random_path(ants+i,levels_needed,root,levels_needed,initial_rels);
		//ant->cost = acqo_calculate_single_ant_path_cost(root,levels_needed,initial_rels,ant);
	}
	//elog(LOG,"acqo: random pathlerin maliyeti hesaplanıyor");
	acqo_calculate_ant_paths_costs(root,levels_needed,initial_rels,ants,ant_count);
	//elog(LOG,"acqo: random pathlerin maliyeti hesaplandı");
	best_random_ant = acqo_select_best_ant(ants,ant_count);

	if(ants[best_random_ant].cost == -1){
		elog(ERROR,"acqo: could not create a random path for query");
	}

	acqo_set_min_max_pheromone(pheromone, ants[best_random_ant].cost,  levels_needed);

	//elog(LOG,"acqo: set_min_pheromone: max,init: %.15f, min: %.15f",pheromone->ph_max, pheromone->ph_min);
	acqo_init_pheromone(pheromone,levels_needed);

	//free allocated memory
	for(i=0;i<ant_count;i++){
		pfree((void*)(ants[i].path));
	}
	pfree((void*)ants);
}

static void acqo_create_random_path(Ant *ant,int node_count,PlannerInfo *root, int levels_needed, List *initial_rels){
	double rand_number;
	int selected_node;
	short *visited_nodes;
	int i,j;
	int visited_node_count = 0;
	RelOptInfo *rl=NULL;
	RelOptInfo *rr=NULL;

	visited_nodes = (short*)palloc(node_count * sizeof(short));
	for(i=0;i<node_count;i++){
		visited_nodes[i] = 0;
	}

	//select firstly desirable tables in order
	for(i=0;i<node_count;i++){
		rand_number = pg_erand48(seed);
		selected_node = (int)floor(rand_number*(node_count-1.00));
		for(j=0;j<node_count;j++){
			if(visited_nodes[selected_node]==0){
				if(rl){
					rr = list_nth(initial_rels,selected_node);
					if(desirable_join(root,rl,rr)){
						ant->path[i] = selected_node;
						visited_nodes[selected_node] = 1;
						rl = rr;
						visited_node_count++;
					}
					break;
				} else {
					ant->path[i] = selected_node;
					visited_nodes[selected_node] = 1;
					rl = list_nth(initial_rels,selected_node);
					visited_node_count++;
					break;
				}
			}
			selected_node = (selected_node+1)%node_count;
		}
	}

	//select randomly
	for(i=0;i<node_count;i++){
		if(visited_node_count==node_count)
			break;
		rand_number = pg_erand48(seed);
		selected_node = (int)floor(rand_number*(node_count-1.00));
		for(j=0;j<node_count;j++){
			if(visited_nodes[selected_node]==0){
				ant->path[i] = selected_node;
				visited_nodes[selected_node] = 1;
				visited_node_count++;
				break;
			}
			selected_node = (selected_node+1)%node_count;
		}
	}

	pfree((void*)visited_nodes);
}
/*
static RelOptInfo *acqo_get_result(PlannerInfo *root, int levels_needed, List *initial_rels,Ant *ant){
	RelOptInfo *result;
	RelOptInfo *next_table;
	int i;

	result = list_nth(initial_rels,ant->path[0]);

	for(i=1;i<levels_needed;i++){
		next_table = list_nth(initial_rels,ant->path[i]);
		if(next_table){
			result = make_join_rel(root,result,next_table);
			if(result){
				generate_partitionwise_join_paths(root, result);
				if(i<levels_needed-1){
					generate_gather_paths(root, result, false);
				}
				set_cheapest(result);
			} else {
				return NULL;
			}
		} else {
			return NULL;
		}
	}

	return result;
}*/

static RelOptInfo *acqo_get_result(PlannerInfo *root, int levels_needed, List *initial_rels,Ant *ant){
	RelOptInfo *result;
	RelOptInfo *next_table;
	List *subjoins = NIL;
	JoinedRel *new_jr;
	ListCell *lc;
	int i;

	for(i=0;i<levels_needed;i++){
		next_table = list_nth(initial_rels,ant->path[i]);
		if(next_table){
			new_jr = (JoinedRel*)palloc(sizeof(JoinedRel));
			new_jr->number_of_rel = 1;
			new_jr->jr = next_table;
			subjoins = acqo_merge_rels(subjoins,root,new_jr,levels_needed,false);
		} else {
			return NULL;
		}
	}


	if(subjoins->length > 1){
		lc = list_head(subjoins);
		new_jr = (JoinedRel*) lfirst(lc);
		subjoins = acqo_merge_rels(subjoins,root,new_jr,levels_needed,true);
	}

	if(subjoins->length == 1){
		lc = list_head(subjoins);
		result = ((JoinedRel*)lfirst(lc))->jr;
	} else {
		result = NULL;
		//elog(ERROR,"acqo: subjoin length: %d",subjoins->length);
	}

	return result;
}

//bu bölüm geqo'daki gimme_tree den uyarlanmıştır
static List* acqo_merge_rels(List* subjoins, PlannerInfo *root, JoinedRel* new_jr, int levels_needed, bool force){
	ListCell *lc,*prev;
	JoinedRel *curjr;
	RelOptInfo *result;

	prev = NULL;

	foreach(lc, subjoins){
		curjr = (JoinedRel*) lfirst(lc);
		if(curjr->jr != new_jr->jr && (desirable_join(root,curjr->jr,new_jr->jr) || force)){
			result = make_join_rel(root,curjr->jr,new_jr->jr);
			if(result){
				generate_partitionwise_join_paths(root, result);

				if(new_jr->number_of_rel + curjr->number_of_rel < levels_needed){
					generate_gather_paths(root, result, false);
				}

				set_cheapest(result);

				subjoins = list_delete_cell(subjoins,lc,prev);
				curjr->number_of_rel += new_jr->number_of_rel;
				curjr->jr = result;

				pfree((void*)new_jr);

				return acqo_merge_rels(subjoins,root,curjr,levels_needed,force);
			}
		}
		prev = lc;
	}

	if (subjoins == NIL || new_jr->number_of_rel == 1)
		return lappend(subjoins, new_jr);

	prev = NULL;
	lc = list_head(subjoins);
	while(1)
	{
		if (lc == NULL || new_jr->number_of_rel > ((JoinedRel *) lfirst(lc))->number_of_rel)
			break;
		prev = lc;
		lc = lnext(lc);
	}

	if(prev == NULL)
		return lcons(new_jr,subjoins);
	else
		lappend_cell(subjoins, prev, new_jr);

	return subjoins;
}

static CostCacheSearchTree *cost_tree;

static double acqo_check_cost_cache(Ant *ant,int levels_needed){
	List* lsp;
	ListCell *lc;
	Ant *cached_ant;
	int i;

	lsp = (cost_tree+ant->path[0]*levels_needed + ant->path[1])->path_list;

	if(lsp == NIL)
		return -2;

	foreach(lc,lsp){
		cached_ant = (Ant*)lfirst(lc);
		if(memcmp(ant->path,cached_ant->path,sizeof(int)*levels_needed) == 0){
			return cached_ant->cost;
		}
	}

	return -2;
}

static void acqo_add_cost_cache(Ant *ant,int levels_needed){
	List* lsp;
	ListCell *lc;
	Ant *cached_ant;

	lsp = (cost_tree+ant->path[0]*levels_needed + ant->path[1])->path_list;
	cached_ant = acqo_init_ants(1,levels_needed);

	acqo_path_copy(cached_ant->path,ant->path,levels_needed);
	cached_ant->cost = ant->cost;

	lsp = lappend(lsp,cached_ant);

	(cost_tree+ant->path[0]*levels_needed + ant->path[1])->path_list = lsp;
}

static double acqo_calculate_single_ant_path_cost(PlannerInfo *root, int levels_needed, List *initial_rels,Ant *ant){
	RelOptInfo *result;
	double cost=-1;
	int	savelength;
	struct HTAB *savehash;
	MemoryContext mycontext;
	MemoryContext oldcxt;

//	elog(LOG,"acqo: cost cache search başlangıcı");
	cost = acqo_check_cost_cache(ant,levels_needed);
//	elog(LOG,"acqo: cost cache search bitişi");

	if(cost != -2){
		return cost;
	} else {
		cost = -1;
	}


	savelength = list_length(root->join_rel_list);
	savehash = root->join_rel_hash;
	mycontext = AllocSetContextCreate(CurrentMemoryContext,
									  "GEQO",
									  ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(mycontext);

	result = acqo_get_result(root,levels_needed,initial_rels,ant);


	if(result){
		cost = result->cheapest_total_path->total_cost;
	} else {
		cost = -1;
	}

	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(mycontext);
	root->join_rel_list = list_truncate(root->join_rel_list, savelength);
	root->join_rel_hash = savehash;

	//elog(LOG,"acqo: join_rel_list uzunluğu, öncesi: %d, sonrası: %d",savelength,list_length(root->join_rel_list));



//	elog(LOG,"acqo: cost cache add başlangıcı");
	acqo_add_cost_cache(ant,levels_needed);
//	elog(LOG,"acqo: cost cache add bitişi");
	return cost;
}


static void acqo_calculate_ant_paths_costs(PlannerInfo *root, int levels_needed, List *initial_rels,Ant *ants,int ant_count){
	int i;

	for(i=0;i<ant_count;i++){
		ants[i].cost = acqo_calculate_single_ant_path_cost(root,levels_needed,initial_rels,&(ants[i]));

	}
}

static void acqo_create_path(PlannerInfo *root, List *initial_rels, Pheromone* pheromone,Ant* ant, int node_count){
	double rand_number;
	int selected_node;
	short *visited_nodes;
	int i;

	visited_nodes = (short*)palloc(node_count * sizeof(short));
	for(i=0;i<node_count;i++){
		visited_nodes[i] = 0;
	}

	//randomly select first node
	rand_number = pg_erand48(seed);
	selected_node = (int)floor(rand_number*(node_count-1.00));
	visited_nodes[selected_node] = 1;
	ant->path[0] = selected_node;

	for(i=1;i<node_count;i++){
		acqo_select_next_node(root,initial_rels,pheromone,ant,i,visited_nodes,node_count);
	}

	pfree((void*)visited_nodes);
}

static void acqo_select_next_node(PlannerInfo *root, List *initial_rels, Pheromone* pheromone,Ant *ant,int next_node_id, short *visited_nodes, int node_count){
	int i;
	int *current_node = &(ant->path[next_node_id-1]);
	int *next_node   = &(ant->path[next_node_id]);
	double total = 0;
	double sub_total = 0;
	double *nodes_probability_factor;
	double rand_number;
	double heuristic_const = 1.0;

	nodes_probability_factor = (double*)palloc(node_count*sizeof(double));

	for(i=0;i<node_count;i++){
		if(visited_nodes[i] == 0) {
			if(desirable_join(root,
							 list_nth(initial_rels,*current_node),
							 list_nth(initial_rels,i))
			){
				heuristic_const = 2.0;
			} else {
				heuristic_const = 1.0;
			}
			nodes_probability_factor[i] = pow(acqo_get_pheromone(pheromone,node_count,*current_node,i),acqo_alfa)*pow(heuristic_const,acqo_beta);
			total = total + nodes_probability_factor[i];
		}
	}
/*
	char dl[4000];
	int t;
	for(i=0,t=0;i<node_count;i++){
		sprintf(dl+t,"%f\t",nodes_probability_factor[i]);
		t = strlen(dl);
	}
	elog(LOG,"acqo: probablity_factor: %s",dl);*/

	rand_number = pg_erand48(seed)*total;
	for(i=0;i<node_count;i++){
		if(visited_nodes[i] == 0) {
			sub_total = sub_total + nodes_probability_factor[i];
			if(rand_number <= sub_total){
				*next_node = i;
				visited_nodes[i] = 1;
				break;
			}
		}
	}

	pfree((void*)nodes_probability_factor);
}

static void acqo_create_paths(PlannerInfo *root, List *initial_rels, Pheromone* pheromone,Ant* ants, int node_count,int ant_count){
	int i;
	int best_ant;

	best_ant = acqo_select_best_ant(ants,ant_count);
	if(ants[best_ant].cost == -1){
		best_ant = -1;
	}

	for(i=0;i<ant_count;i++){
		//if(i != best_ant){
			acqo_create_path(root,initial_rels,pheromone,&(ants[i]),node_count);
		//}
	}
}

static int acqo_select_best_ant(Ant* ants,int ant_count){
	int best_ant;
	int i;

	best_ant = 0;
	for(i=1;i<ant_count;i++){
		if((ants[i].cost != -1 && ants[best_ant].cost == -1) ||
		   (ants[i].cost != -1 && ants[i].cost < ants[best_ant].cost)){
			best_ant = i;
		}
	}

	return best_ant;
}

static void acqo_init_pheromone(Pheromone *pheromone,int node_count){
	int i,j;

	for(i=0;i<node_count;i++){
		for(j=0;j<node_count;j++){

			acqo_set_pheromone(pheromone,node_count,i,j,pheromone->ph_init);
		}
	}
}
/*
static void acqo_multiply_pheromone_to_all(Pheromone *pheromone,int node_count,double factor){
	int i,j;
	double new_amount;

	for(i=0;i<node_count;i++){
		for(j=0;j<node_count;j++){
			new_amount = acqo_get_pheromone(pheromone,node_count,i,j)*factor;
			acqo_set_pheromone(pheromone,node_count,i,j,new_amount);
		}
	}
}*/

static void acqo_evaporate_pheromones(Pheromone *pheromone,int node_count){
	int i,j;
	double amount_of_pheromone;

	//evaporate pheromones
	for(i=0;i<node_count;i++){
		for(j=0;j<node_count;j++){
			amount_of_pheromone = acqo_get_pheromone(pheromone,node_count,i,j);
			amount_of_pheromone = (1-acqo_evaporation_level) * amount_of_pheromone;
			if(amount_of_pheromone < pheromone->ph_min){
				amount_of_pheromone = pheromone->ph_min;
			}
			acqo_set_pheromone(pheromone,node_count,i,j,amount_of_pheromone);
		}
	}
}

static void acqo_deposit_pheromone(Pheromone *pheromone,Ant* ant,int node_count){
	double amount_of_deposit_pheromone = 0;
	int current_node,next_node,i;
	double amount_of_pheromone;

	//Eğer geçerli bir yol bulunabildi ise pheromone eklemesi yap
	if(ant->cost != -1) {
		amount_of_deposit_pheromone = 1.0/ant->cost;
		current_node = ant->path[0];
		for(i=1;i<node_count;i++){
			next_node = ant->path[i];
			amount_of_pheromone = acqo_get_pheromone(pheromone, node_count, current_node, next_node) + amount_of_deposit_pheromone;
			if(amount_of_pheromone > pheromone->ph_max){
				amount_of_pheromone = pheromone->ph_max;
			}
			acqo_set_pheromone(pheromone, node_count, current_node, next_node, amount_of_pheromone);
			current_node = next_node;
		}
	}

	//elog(LOG,"acqo: deposit: %.15f",amount_of_deposit_pheromone);
}

static void acqo_update_pheromones(Pheromone *pheromone,Ant* ant,int node_count){
	acqo_evaporate_pheromones(pheromone, node_count);
	acqo_deposit_pheromone(pheromone, ant, node_count);
}

static RelOptInfo *
acqo_join_planner(PlannerInfo *root, int levels_needed, List *initial_rels)
{
	int ant_count,best_ant=0,i,j,k;
	RelOptInfo * result;
	Pheromone* pheromone;
	Ant *ants;
	Ant *global_best_ant;
	char dl[8000];

//	double t_create_path = 0,t_calculate_cost=0,t_best_ant=0,t_local_search=0,t_update_pheromone=0,t_init=0;

	int t;

	//If acqo disables, run geqo join search
	if (acqo_enable == false){
		if(acqo_force_geqo)
			return geqo(root, levels_needed, initial_rels);
		else
			return standard_join_search(root, levels_needed, initial_rels);
	}

//	start_timers();
	seed[0] = 0;
	seed[1] = 0;
	seed[2] = 0;
	memcpy(seed,&acqo_seed,sizeof(seed));

	//elog(LOG,"acqo: levels needed: %d",levels_needed);

	if(acqo_ant_count == 0){
		ant_count = levels_needed;
	} else {
		ant_count = acqo_ant_count;
	}

	cost_tree = (CostCacheSearchTree*)palloc(levels_needed*levels_needed*sizeof(CostCacheSearchTree));
	for(i=0;i<levels_needed*levels_needed;i++){
		cost_tree[i].path_list = NIL;
	}

	//create pheromone matrix
	pheromone = acqo_init_nn_pheromone_matrix(levels_needed);

	//create ants
	ants = acqo_init_ants(ant_count,levels_needed);
	global_best_ant = acqo_init_ants(1,levels_needed);

	//initialize pheromone matrix
	acqo_set_min_pheromone(pheromone,root,levels_needed,initial_rels);
	//elog(LOG,"acqo: init pheromone değeri: %f",pheromone->ph_init);

//	t_init = elapsed_time(REAL);
	if(acqo_print_debug)
		elog(LOG,"acqo: round'a baslıyor");
	//start rounds
	for(i=0;i<acqo_round_count;i++){
//		start_timers();
		acqo_create_paths(root,initial_rels,pheromone,ants,levels_needed,ant_count);
		if(acqo_print_debug)
			elog(LOG,"acqo: round %d için pathler oluşturuldu",i);
//		t_create_path += elapsed_time(REAL);

//		start_timers();
		acqo_calculate_ant_paths_costs(root,levels_needed,initial_rels,ants,ant_count);
		if(acqo_print_debug)
			elog(LOG,"acqo: round %d için costlar hesaplandı",i);
//		t_calculate_cost += elapsed_time(REAL);

//		start_timers();
		best_ant = acqo_select_best_ant(ants,ant_count);
		if(acqo_print_debug)
			elog(LOG, "acqo: round %d için en iyi karınc seçildi, karınca: %d",i,best_ant);
//		t_best_ant += elapsed_time(REAL);

//		start_timers();
		acqo_local_search_2opt(&(ants[best_ant]),root,levels_needed,initial_rels);
//		t_local_search += elapsed_time(REAL);

		/*if(ants[best_ant].cost*2.0 <= pheromone->base_cost ){
			double old_phmin;
			old_phmin = pheromone->ph_min;
			acqo_set_min_max_pheromone(pheromone,ants[best_ant].cost,levels_needed);
			acqo_multiply_pheromone_to_all(pheromone,levels_needed,old_phmin/pheromone->ph_min);
		}*/

//		start_timers();
		acqo_update_pheromones(pheromone,&(ants[best_ant]),levels_needed);
		if(acqo_print_debug)
			elog(LOG,"acqo: round %d için feromonlar güncellendi, round tamamlandı",i);
//		t_update_pheromone += elapsed_time(REAL);

		if(ants[best_ant].cost != -1 && (
				global_best_ant->cost == -1 ||
				global_best_ant->cost > ants[best_ant].cost
			)
		){
			acqo_path_copy(global_best_ant->path,ants[best_ant].path,levels_needed);
			global_best_ant->cost = ants[best_ant].cost;
		}

/*
		t=0;
		for(j=0;j<ant_count;j++){
			if(j==best_ant){
				sprintf(dl+t,"\n**Path of ant #%d : ", j);
			} else {
				sprintf(dl+t,"\nPath of ant #%d : ", j);
			}
			for(k=0;k<levels_needed;k++){
				t = strlen(dl);
				sprintf(dl+t,"%d ",ants[j].path[k]);
			}
			t = strlen(dl);
			sprintf(dl+t,"-> cost: %f",ants[j].cost);
			t = strlen(dl);
		}
		elog(LOG,"acqo: %s",dl);
*/
		//pheromone matrisini yazdır
		if(acqo_print_pheromone){
			k=0;
			for(t=0;t<levels_needed;t++){
				sprintf(dl+k,"\n");
				k = strlen(dl);
				for(j=0;j<levels_needed;j++){
					sprintf(dl+k,"%.15f\t", acqo_get_pheromone(pheromone,levels_needed,t,j));
					k = strlen(dl);
				}
			}
			sprintf(dl+k,"\n");
			k = strlen(dl);
			elog(LOG,"acqo: %s",dl);
		}
	}

	//elog(LOG,"acqo: Harcanan sureler, init: %.10f\tcreate_path: %.10f\tcalculate_cost: %.10f\tselect_best_ant: %.10f\tlocal_search: %.10f\tupdate_pheromone: %.10f\t",t_init,t_create_path,t_calculate_cost,t_best_ant,t_local_search,t_update_pheromone);

	/* Geçici bölüm başlangıcı */
	//acqo_create_random_path(ants,levels_needed);


	/* Geçici bölüm sonu */
	if(ants[best_ant].cost != -1){
		result = acqo_get_result(root,levels_needed,initial_rels,global_best_ant);
	} else {
		result = NULL;
	}


	if(result){
		if(acqo_print_debug){
			elog(LOG,"acqo: join üretildi");
		}
	} else {
		elog(LOG,"acqo: join üretilemedi!!!!");
	}


	//Free allocated memory
	pfree((void*)(pheromone->pheromone_matrix));
	pfree((void*)pheromone);

	for(i=0;i<ant_count;i++)
		pfree((void*)(ants[i].path));

	pfree((void*)ants);

	//elog(LOG,"alınan bellekler bırakıldı");

	return result;
}

static void load_params(){
	DefineCustomIntVariable("acqo.ant_count",
							"Ant count for ant colony optimization",
							 NULL,
							 &acqo_ant_count,
							 0, 0, 500,
							 PGC_USERSET,
							 0, NULL, NULL, NULL);

	DefineCustomIntVariable("acqo.round_count",
							"Round count for ant colony optimization",
							 NULL,
							 &acqo_round_count,
							 50, 0, 500,
							 PGC_USERSET,
							 0, NULL, NULL, NULL);

	DefineCustomBoolVariable("acqo",
			 	 	 	 	 "Enable or disable ant colony optimization",
							 NULL,
							 &acqo_enable,
							 true,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomBoolVariable("acqo.enable",
			 	 	 	 	 "Enable or disable ant colony optimization",
							 NULL,
							 &acqo_enable,
							 true,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomBoolVariable("acqo.force_geqo",
			 	 	 	 	 "on -> force geqo, off -> force standard join (if acqo is disabled)",
							 NULL,
							 &acqo_force_geqo,
							 true,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomBoolVariable("acqo.print_pheromone",
			 	 	 	 	 "Enable or disable printing pheromone matrix",
							 NULL,
							 &acqo_print_pheromone,
							 false,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomBoolVariable("acqo.debug_lines",
			 	 	 	 	 "Enable or disable printing debug lines matrix",
							 NULL,
							 &acqo_print_debug,
							 false,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomRealVariable("acqo.beta",
							 "beta of ant colony query optimization",
							 NULL,
							 &acqo_beta,
							 0,
							 0.0,
							 5.0,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomRealVariable("acqo.alfa",
							 "alfa factor of ant colony query optimization",
							 NULL,
							 &acqo_alfa,
							 1,
							 0.0,
							 5.0,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);

	DefineCustomRealVariable("acqo.seed",
							 "alfa factor of ant colony query optimization",
							 NULL,
							 &acqo_seed,
							 0,
							 0.0,
							 1.0,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);


	DefineCustomRealVariable("acqo.evaporation_level",
							 "evaporation level of each global pheromone update of acqo",
							 NULL,
							 &acqo_evaporation_level,
							 0.02,
							 0.0,
							 1.0,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);
}

//geqo'dan alınmıştır. (geqo_eval.c)
static bool
desirable_join(PlannerInfo *root,
			   RelOptInfo *outer_rel, RelOptInfo *inner_rel)
{
	/*
	 * Join if there is an applicable join clause, or if there is a join order
	 * restriction forcing these rels to be joined.
	 */
	if (have_relevant_joinclause(root, outer_rel, inner_rel) ||
		have_join_order_restriction(root, outer_rel, inner_rel))
		return true;

	/* Otherwise postpone the join till later. */
	return false;
}


void
_PG_init(void)
{
	/* get configuration */
	load_params();

	/* switch hooks */
	prev_join_search_hook = join_search_hook;
	join_search_hook = acqo_join_planner;
}

void
_PG_fini(void)
{
	/* reinstall default hook */
	join_search_hook = prev_join_search_hook;
}
