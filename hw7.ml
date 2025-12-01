(* SECTION 1 *)

(*  Question 1.1 *)
let rec repeat (x : 'a) : 'a stream = 
  {
    head = x;
    tail = Susp (fun () -> (repeat x));
  }
  

(* Question 1.2 *)
let rec filter (f : 'a -> bool) (s : 'a stream) : 'a stream = 
  if f s.head then 
    {
      head = s.head;
      tail = Susp (fun () -> filter f (force s.tail));
    }
  else
    filter f (force s.tail)
      
(* Question 1.3 *)
let rec lucas1 =
  {
    (* You should fix these *)
    head = 2;
    tail = Susp (fun () -> lucas2);
  }

and lucas2 =
  {
    (* You should fix these *)
    head = 1;
    tail = Susp (fun () -> zip_with (fun x y -> x + y) lucas1 lucas2);
  }

(* Question 1.4 *)
let unfold (f : 'a -> 'b * 'a) (seed : 'a) : 'b stream = 
  let s = iterate (fun (b, a) -> f a) (f seed) in
  let (x, y) = s.head in
  {
    head = x;
    tail = Susp (fun () -> map (fun (b, a) -> b) (force s.tail));
  }

(* Question 1.5 *)
let unfold_lucas : int stream = 
  unfold (fun (x,y) -> (x, (y, x + y))) (2, 1)

(* SECTION 2 *)

(* Question 2.1 *)
let rec scale (s1 : int stream) (n : int) : int stream = 
  {
    head = (s1.head * n);
    tail = Susp (fun () -> map (fun x -> x * n) (force s1.tail));
  } 

(* Question 2.2 *) 
let rec s = 
  {
    head = 1;
    tail = Susp (fun () -> let 
                  s_2 = scale s 2
                  and 
                    s_3 = scale s 3
                  and 
                    s_5 = scale s 5
                  in
                  (merge s_2 (merge s_3 s_5)));
  }
  
