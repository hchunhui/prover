#include <stdio.h>

int abs(int a)
{
	return a<0?-a:a;
}

int main(int argc, char *argv[])
{
	int i, j;
	char line[128];
	for(j = 0;gets(line);)
	{
		int a[4];
		if(line[0] == 'c' || line[0] == 'p' || line[0] == '%' || line[0] == '0')
			continue;
		sscanf(line, "%d %d %d %d", a, a+1, a+2, a+3);
		if(j)
			printf("/\\");
		printf("(");
		for(i = 0; i < 3; i++)
		{
			printf("%s%sA%d",
			       i?"\\/":"",
			       a[i]<0?"~":"",
			       abs(a[i]));
		}
		printf(")");
		j++;
	}
	return 0;
}
