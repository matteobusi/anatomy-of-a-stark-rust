fn iexp (a : i128, b : i128) -> i128 {
    let mut res = 1;
    let mut _a = a;
    let mut _b = b;

    while _b > 0 {
        println!("a = {:?}; b = {:b}; res = {:?}", _a, _b, res);
        if (_b % 2) == 1 {
            res *= _a;
        }
        _a *= _a;
        _b >>= 1;
    }

    res
}


fn main() {
    println!("{:?} ^ {:?} = {:?}", 5, 13, iexp(5, 13));
}
