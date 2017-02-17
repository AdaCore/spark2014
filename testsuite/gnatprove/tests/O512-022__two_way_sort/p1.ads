package P1 is
   subtype Index is Integer range 0 .. 1_000_000;
   type Arr is array (Index range <>) of Boolean;
   procedure Two_Way_Sort (A : in out Arr) with
     Post => A'Last < A'First
               or else (for some K in A'Range =>
			  (for all J in A'First .. K => not A(J))
			    and then (for all J in K+1 .. A'Last => A(J)));
end P1;
