method test(i: int) returns (j: int)
    requires i >= 0
    ensures j == i {
    if (i == 0) {
        j:= i;
    } else {
        j := i + 1;
        if (i == 1) {
            j := i;
        }
        
    }
}