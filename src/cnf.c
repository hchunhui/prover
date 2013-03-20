#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "list.h"
#include "etree.h"
#include "cnf.h"

/*
 * 第一步：消除蕴含词
 */
static void simp_impl(struct etree *p)
{
	struct etree *t;
	switch(p->type)
	{
	case T_IMPL:
		t = etree_mknode(T_NOT, 0, p->l, NULL);
		p->l = t;
		p->type = T_OR;
		simp_impl(p->l);
		simp_impl(p->r);
		break;
	case T_OR:
	case T_AND:
		simp_impl(p->l);
		simp_impl(p->r);
		break;
	case T_NOT:
		simp_impl(p->l);
		break;
	}
}

static void __proof_imp(struct etree *p)
{

	struct etree *t;
	switch(p->type)
	{
	case T_IMPL:
		printf("(iff_trans _ _ _ (L_imp _ _ _ _ (");
		__proof_imp(p->l);
		printf(") (");
		__proof_imp(p->r);
		printf(")) (imp_or _ _))");
		break;
	case T_AND:
		printf("(L_and _ _ _ _ (");
		__proof_imp(p->l);
		printf(") (");
		__proof_imp(p->r);
		printf("))");
		break;
	case T_OR:
		printf("(L_or _ _ _ _ (");
		__proof_imp(p->l);
		printf(") (");
		__proof_imp(p->r);
		printf("))");
		break;
	case T_NOT:
		printf("(L_not _ _ (");
		__proof_imp(p->l);
		printf("))");
		break;
	case T_PROP:
		printf("(imp_p A%d)", p->val);
		break;
	}
}

void proof_impl(struct etree *p)
{
	printf("Definition elim_impl:=(");
	__proof_imp(p);
	printf(").\nCheck (elim_impl).\n");
	simp_impl(p);
}

/*
 * 第二步：否定词深入
 */
static void simp_not1(struct etree *p, int not)
{
	struct etree *t;
	switch(p->type)
	{
	case T_NOT:
		simp_not1(p->l, !not);
		break;
	case T_OR:
		if(not)
			p->type = T_AND;
		goto comm_case;
	case T_AND:
		if(not)
			p->type = T_OR;
	comm_case:
		if(not) {
			t = etree_mknode(0, 0, NULL, NULL);
			memcpy(t, p, sizeof(struct etree));
			p->type = T_NOT;
			p->l = t;
			p->r = NULL;
			p = p->l;
			t = etree_mknode(T_NOT, 0, p->l, NULL);
			p->l = t;
			t = etree_mknode(T_NOT, 0, p->r, NULL);
			p->r = t;
		}
		simp_not1(p->l, 0);
		simp_not1(p->r, 0);
		break;
	}
}

static void simp_not2(struct etree *p, int not)
{
	struct etree *t;
	switch(p->type)
	{
	case T_NOT:
		t = p->l;
		memcpy(p, t, sizeof(struct etree));
		free(t);
		simp_not2(p, !not);
		break;
	case T_OR:
	case T_AND:
		simp_not2(p->l, not);
		simp_not2(p->r, not);
		break;
	case T_PROP:
		if(not)
			p->val = -p->val;
		break;
	}
}

static void __proof_not1(struct etree *p, int not)
{
	const char *pc1;
	switch(p->type)
	{
	case T_NOT:
		printf("(L_not _ _ (");
		__proof_not1(p->l, !not);
		printf("))");
		break;
	case T_OR:
		pc1 = "or";
		goto comm_case;
	case T_AND:
		pc1 = "and";
	comm_case:
		if(not) {
			printf("(iff_trans _ _ _ (L_%s _ _ _ _ (", pc1);
			__proof_not1(p->l, not);
			printf(") (");
			__proof_not1(p->r, not);
			printf(")) (n%s _ _))", pc1);
		} else {
			printf("(L_%s _ _ _ _ (", pc1);
			__proof_not1(p->l, not);
			printf(") (");
			__proof_not1(p->r, not);
			printf("))");
		}
		break;
	case T_PROP:
		printf("(imp_p A%d)", p->val);
		break;
	}
}

static void __proof_not2(struct etree *p, int not)
{
	const char *pc1;
	switch(p->type)
	{
	case T_NOT:
		if(not) {
			printf("(iff_trans _ _ _ (L_not _ _ (L_not _ _ (");
			__proof_not2(p->l, 0);
			printf("))) (np _))");
		} else {
			__proof_not2(p->l, 1);
		}
		break;
	case T_OR:
		pc1 = "or";
		goto comm_case;
	case T_AND:
		pc1 = "and";
	comm_case:
		if(not) {
			printf("(L_not _ _ (");
		}
		printf("(L_%s _ _ _ _ (", pc1);
		__proof_not2(p->l, 0);
		printf(") (");
		__proof_not2(p->r, 0);
		printf("))");
		if(not) {
			printf("))");
		}
		break;
	case T_PROP:
		if(not) {
			printf("(L_not _ _ (");
		}
		printf("(imp_p A%d)", p->val);
		if(not) {
			printf("))");
		}
		break;
	}
}

void proof_not(struct etree *p)
{
	printf("Definition insert_not1:=(");
	__proof_not1(p, 0);
	printf(").\nCheck (insert_not1).\n");
	simp_not1(p, 0);
	printf("Definition insert_not2:=(");
	__proof_not2(p, 0);
	printf(").\nCheck (insert_not2).\n");
	printf("Definition L0':= "
	       "(iff_imp _ _ "
	       "(iff_trans _ _ _ elim_impl (iff_trans _ _ _ insert_not1 insert_not2)) "
	       "L0).\n");
	simp_not2(p, 0);
}

/*
 * 第三步：求析取范式各析取支
 */
static struct etree *simp_dist1(struct etree *t1, struct etree *t2)
{
	struct etree *t;
	if(t1->type == T_AND)
	{
		t = etree_mknode(T_AND,
				 0,
				 simp_dist1(t1->l, t2),
				 simp_dist1(t1->r, t2));
//		free(t1);
	}
	else if(t2->type == T_AND)
	{
		t = etree_mknode(T_AND,
				 0,
				 simp_dist1(t1, t2->l),
				 simp_dist1(t1, t2->r));
//		free(t2);
	}
	else
	{
		t = etree_mknode(T_OR,
				 0,
				 t1,
				 t2);
	}
	return t;
}

static struct etree *simp_dist(struct etree *p)
{
	struct etree *t1, *t2, *t;
	switch(p->type)
	{
	case T_AND:
		return etree_mknode(T_AND, 0, simp_dist(p->l), simp_dist(p->r));
	case T_OR:
		t1 = simp_dist(p->l);
		t2 = simp_dist(p->r);
		t = simp_dist1(t1, t2);
		return t;
	case T_PROP:
		return etree_mknode(T_PROP, p->val, NULL, NULL);
	}
}

static void __cons_clause(struct etree *p, struct list *list)
{
	switch(p->type)
	{
	case T_PROP:
		if(p->val > 0)
			list->cp |= 1ull << (p->val-1);
		else
			list->cn |= 1ull << (-p->val-1);
		break;
	case T_OR:
		__cons_clause(p->l, list);
		__cons_clause(p->r, list);
		break;
	}
}

static struct list *cons_clause(struct etree *p)
{
	struct list *cl1, *cl2, *cl;
	switch(p->type)
	{
	case T_AND:
		cl1 = cons_clause(p->l);
		cl2 = cons_clause(p->r);
		for(cl = cl1; cl->next; cl = cl->next);
		cl->next = cl2;
		return cl1;
	default:
		cl = list_new();
		cl->cp = 0;
		cl->cn = 0;
		__cons_clause(p, cl);
		return cl;
	}
}

static int __proof_genor(struct etree *p, struct list *goal, int hc)
{
	int vec1[128], vec2[128], vec[128];
	int n1, n2, n;
	int rank[128];
	n1 = bit2vec(goal->cp, goal->cn, vec1);
	vec2[0] = p->val;
	n2 = 1;
	n = or_merge(vec1, n1, vec2, n2, rank, vec);
	or_intro(rank[p->val>0?p->val-1:(63-p->val)], vec, n, hc);
	return 1;
}

static int __goal_include(struct etree *p, struct list *goal)
{
	switch(p->type)
	{
	case T_OR:
		return __goal_include(p->l, goal) && __goal_include(p->r, goal);
	case T_AND:
		return __goal_include(p->l, goal) || __goal_include(p->r, goal);
	case T_PROP:
		if(p->val < 0 && (goal->cn & (1ull<<(-p->val-1))) ||
		   (p->val > 0 && (goal->cp & (1ull<<(p->val-1)))))
			return 1;
		return 0;
	}
	return 0;
}

static int __proof_dist(struct etree *p, int from, int hc, struct list *goal)
{
	int thc;
	switch(p->type)
	{
	case T_AND:
		thc = hc;
		printf("(and_ind (fun (H%d:", hc++);
		etree_dump_infix(p->l, stdout);
		printf(") (H%d:", hc++);
		etree_dump_infix(p->r, stdout);
		printf(") => (");
		if(__goal_include(p->l, goal))
			hc = __proof_dist(p->l, thc, hc, goal);
		else if(__goal_include(p->r, goal))
			hc = __proof_dist(p->r, thc+1, hc, goal);
		printf("))H%d)\n", from);
		break;
	case T_OR:
		thc = hc;
		printf("(or_ind\n");
		printf("(fun (H%d:", hc++);
		etree_dump_infix(p->l, stdout);
		printf(") => (");
		hc = __proof_dist(p->l, thc, hc, goal);
		printf("))\n");
		thc = hc;
		printf("(fun (H%d:", hc++);
		etree_dump_infix(p->r, stdout);
		printf(") => (");
		hc = __proof_dist(p->r, thc, hc, goal);
		printf("))\n");
		printf("H%d)\n", from);
		break;
	case T_PROP:
		if(!__proof_genor(p, goal, from)) {
			fprintf(stderr, "bad\n");
			exit(1);
		}
		break;
	}
	return hc;
}

struct list *proof_dist(struct etree *p)
{
	struct etree *t;
	struct list *list, *pl;
	int i;
	t = simp_dist(p);
	etree_dump_prefix(t, stderr);
	fprintf(stderr, "\n");
	list = cons_clause(t);
	for(pl = list, i = 1; pl; pl = pl->next, i++)
	{
		printf("Definition _L%d:=(fun (H0:", i);
		etree_dump_infix(p, stdout);
		printf(") =>\n");
		__proof_dist(p, 0, 1, pl);
		printf(").\nCheck (_L%d).\n", i);
		pl->seq = i;
	}
//	etree_destroy(t);
	return list;
}
