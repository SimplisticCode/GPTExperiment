#define is_turn_A (turn == false)
#define is_turn_B (turn == true)
#define flag_A (flag[0] == true)
#define flag_B (flag[1] == true)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
ltl mutual_exclusion { [](cnt <= 1) }
ltl valid_cnt_values { [](cnt_zero || cnt_one) }
ltl eventual_entry_A { [](flag_A -> <> cnt_one) }
ltl eventual_entry_B { [](flag_B -> <> cnt_one) }
ltl turn_alternation { []((is_turn_A -> <> is_turn_B) && (is_turn_B -> <> is_turn_A)) }
bool turn;
bool flag[2];
byte cnt;
active proctype ProcessA(){
	int i = 0;
	int j = 1;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = i;
		flag[i] = false;
	od;
}
active proctype ProcessB(){
	int i = 1;
	int j = 0;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = j;
		flag[i] = false;
	od;
}
