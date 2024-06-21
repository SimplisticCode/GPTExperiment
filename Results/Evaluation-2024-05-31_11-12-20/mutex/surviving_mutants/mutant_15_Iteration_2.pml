#define is_turn_0 (turn == false)
#define is_turn_1 (turn == true)
#define flag_0_true (flag[0] == true)
#define flag_0_false (flag[0] == false)
#define flag_1_true (flag[1] == true)
#define flag_1_false (flag[1] == false)
#define cnt_0 (cnt == 0)
#define cnt_1 (cnt == 1)
#define flag_0_reset (flag[0] == false)
#define flag_1_reset (flag[1] == false)
#define turn_correct_A (turn == true)
#define turn_correct_B (turn == false)
#define progress_A (flag[0] == true)
#define progress_B (flag[1] == true)
ltl mutual_exclusion { [] (cnt <= 1) }
ltl flag_validity { [] ((flag_0_true || flag_0_false) && (flag_1_true || flag_1_false)) }
ltl turn_validity { [] (is_turn_0 || is_turn_1) }
ltl eventual_entry_A { <> (cnt_1 && is_turn_0) }
ltl eventual_entry_B { <> (cnt_1 && is_turn_1) }
ltl flag_reset_A { [] (flag_0_true -> <> flag_0_false) }
ltl flag_reset_B { [] (flag_1_true -> <> flag_1_false) }
ltl flag_reset_after_critical_A { [] (cnt_0 -> <> flag_0_reset) }
ltl flag_reset_after_critical_B { [] (cnt_0 -> <> flag_1_reset) }
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
		flag[i] = true;
	od;
}
