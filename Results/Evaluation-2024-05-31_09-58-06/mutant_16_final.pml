#define is_turn_A (turn == false)
#define is_turn_B (turn == true)
#define flag_A (flag[0] == true)
#define flag_B (flag[1] == true)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
ltl mutual_exclusion { [] (cnt <= 1) }
ltl eventual_entry_A { [] (flag_A -> <> cnt_one) }
ltl eventual_entry_B { [] (flag_B -> <> cnt_one) }
ltl turn_alternation { [] (is_turn_A -> <> is_turn_B) && [] (is_turn_B -> <> is_turn_A) }
ltl reset_flag_A { [] (cnt_zero -> (flag_A -> <> !flag_A)) }
ltl reset_flag_B { [] (cnt_zero -> (flag_B -> <> !flag_B)) }
ltl reset_flag_A_after_critical { [] (cnt_zero -> (flag[0] -> <> !flag[0])) }
ltl reset_flag_B_after_critical { [] (cnt_zero -> (flag[1] -> <> !flag[1])) }
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
		turn = j;
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
			:: turn > j;
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
