#define valid_i (i >= 0 && i <= 4)
#define array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define array_set (array[i] == i)
ltl valid_i_always { [] valid_i }
ltl array_correct_eventually { <> array_correct }
ltl array_set_eventually { [] (i < 4 -> <> array_set) }
ltl process_completes { <> (i == 4) }
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
