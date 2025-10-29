pub fn superscript(v: usize) -> String {
    let v = v.to_string();
    let mut res = String::with_capacity(v.len());

    for char in v.chars() {
        let sup = match char {
            '0' => '⁰',
            '1' => '¹',
            '2' => '²',
            '3' => '³',
            '4' => '⁴',
            '5' => '⁵',
            '6' => '⁶',
            '7' => '⁷',
            '8' => '⁸',
            '9' => '⁹',
            _ => unreachable!(),
        };

        res.push(sup);
    }

    res
}
