#define valid_index (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define index_reaches_end (i == 4)
ltl valid_index_range { [] valid_index }
ltl eventually_correct_array { <> array_correct }
ltl eventually_end_index { <> index_reaches_end }
ltl correct_array_at_end { [] (index_reaches_end -> array_correct) }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i >= 4;
		array[i] = i;
		i++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
