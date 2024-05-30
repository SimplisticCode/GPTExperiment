#define is_i_valid (i >= 0 && i <= 4)
#define is_array_correct (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i_range { [] is_i_valid }
ltl eventually_correct_array { <> is_array_correct }
ltl eventually_terminate { <> (i == 4) }
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
