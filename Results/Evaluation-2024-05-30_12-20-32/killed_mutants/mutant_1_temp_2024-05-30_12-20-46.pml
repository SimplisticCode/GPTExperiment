#define valid_index (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define index_complete (i == 4)
ltl valid_index_always { [] valid_index }
ltl eventually_array_correct { <> array_correct }
ltl eventually_index_complete { <> index_complete }
ltl array_correct_when_index_complete { [] (index_complete -> array_correct) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: array[3] < 4;
		array[i] = i;
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
