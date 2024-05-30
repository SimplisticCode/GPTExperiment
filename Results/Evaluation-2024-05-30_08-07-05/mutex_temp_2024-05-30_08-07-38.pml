#define is_turn0 (turn == 0)
#define is_turn1 (turn == 1)
#define flag0_true (flag[0] == true)
#define flag0_false (flag[0] == false)
#define flag1_true (flag[1] == true)
#define flag1_false (flag[1] == false)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
ltl valid_cnt { [](cnt_zero || cnt_one) }
ltl valid_flags { [](flag0_true || flag0_false) && (flag1_true || flag1_false) }
ltl valid_turn { [](is_turn0 || is_turn1) }
ltl mutual_exclusion { [](cnt <= 1) }
ltl progress_A { [](flag0_true -> <> cnt_one) }
ltl progress_B { [](flag1_true -> <> cnt_one) }
ltl alternation_A { [](cnt_one -> <> cnt_zero) }
ltl alternation_B { [](cnt_one -> <> cnt_zero) }
bool turn;
bool flag[2];
byte cnt;

active proctype ProcessA()
{
    int i = 0; // Assuming process A has a fixed id of 0
    int j = 1;
    do
    :: true -> // Replaces the againA label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}

active proctype ProcessB()
{
    int i = 1; // Assuming process B has a fixed id of 1
    int j = 0;
    do
    :: true -> // Replaces the againB label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}
