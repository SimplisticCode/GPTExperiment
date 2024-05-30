#define is_i_valid (i >= 0 && i <= 4)
#define is_array_valid (array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3)
#define is_array_initialized (array[0] == 0 && array[1] == 0 && array[2] == 0 && array[3] == 0)
#define is_i_incremented (i == 0 || i == 1 || i == 2 || i == 3 || i == 4)

ltl valid_i { [] is_i_valid }
ltl valid_array_initialization { <> is_array_initialized }
ltl array_values_set_correctly { [] (i == 4 -> is_array_valid) }
ltl valid_array_correct { <> is_array_valid }

int array[4];
int i = 0;

active proctype test (){
	do
	:: i < 4 ->
		array[i] = i;
		i++;
	:: else ->
		skip;
	od;
	assert(array[0] == 0 && array[1] == 1 && array[2] == 2 && array[3] == 3);
}