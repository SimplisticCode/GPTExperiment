#define is_turn_0 (turn == false)
#define is_turn_1 (turn == true)
#define flag_0_true (flag[0] == true)
#define flag_1_true (flag[1] == true)
#define cnt_0 (cnt == 0)
#define cnt_1 (cnt == 1)
ltl valid_cnt { [](cnt_0 || cnt_1) }
ltl mutual_exclusion { [](cnt_1 -> (flag_0_true || flag_1_true)) }
ltl eventually_critical_A { <> (cnt_1 && flag_0_true) }
ltl eventually_critical_B { <> (cnt_1 && flag_1_true) }
ltl flag_0_leads_to_critical { [](flag_0_true -> <> (cnt_1 && flag_0_true)) }
ltl flag_1_leads_to_critical { [](flag_1_true -> <> (cnt_1 && flag_1_true)) }
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
