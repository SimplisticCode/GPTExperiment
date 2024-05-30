#define is_i_valid (i >= 0 && i <= 4)
#define is_array_valid (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
ltl valid_i_range { [] is_i_valid }
ltl valid_array_values { [] (i == 4 -> is_array_valid) }
ltl eventually_i_4 { <> (i == 4) }
ltl eventually_valid_array { <> is_array_valid }
int array[4];
int i = 0;
active proctype test(){
	do
	:: i < 4;
		array[i] = i;
		array[1]++;
	:: else;
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}
