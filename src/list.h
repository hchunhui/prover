#ifndef _LIST_H_
#define _LIST_H_

struct list
{
	struct list *next;
	struct list *f1, *f2;
	int seq;
	unsigned long long cp, cn;
};

static struct list *list_new()
{
	struct list *p;
	p = malloc(sizeof(struct list));
	p->next = NULL;
	p->f1 = NULL;
	p->f2 = NULL;
	p->seq = 0;
	return p;
}

static void list_free(struct list *p)
{
	free(p);
}

static int list_insert(struct list **head, struct list *p)
{
	struct list *it;
	for(it = *head;it;it = it->next)
		if(it->cp == p->cp && it->cn == p->cn)
			return 0;
	p->next = *head;
	*head = p;
	return 1;
}


#endif /* _LIST_H_ */
