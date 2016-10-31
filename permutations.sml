fun concat(x : ''a )(nil : ''a list list) = nil
	|concat(x : ''a)(y::ys : ''a list list) = (x::y)::concat(x)(ys);
fun remove(elem)(xs) = List.filter(fn x => x <> elem) (xs);
local
	fun new_map(f)(nil) = nil
			|new_map(f)(x::xs) = f(x) @ (new_map(f)(xs));
in
	fun permute(nil : ''a list) = [[]]
		|permute(x::nil : ''a list) = [[x]]
		|permute(xs) = new_map(generate_one_perm(xs)) (xs)
		and generate_one_perm(xs: ''a list)(x : ''a) = concat(x) (permute( remove(x)(xs) ) );
end


	


