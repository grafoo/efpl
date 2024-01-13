#eval 61 == 42 + 19
#eval "ABC" == String.append "A" (String.append "B" "C")
#eval "ABC" == String.append (String.append "A" "B") "C"
#eval 5 == if 3 == 3 then 5 else 7
#eval "not equal" == if 3 == 4 then "equal" else "not equal"
