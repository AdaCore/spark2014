package Tab is
   subtype Index is Integer range 1 .. 10;
   type Arr is array (Index) of Integer;
   procedure Tab_Filter (B : in Arr; Threshold : in Integer; A : in out Arr)
   -- Each non negative value in B[1] .. B[10] is equal to one of A[1] .. A[10]
   with Post => (for all J in Index =>
                   (if (B(J) > Threshold) then
                      (for some K in Index => A(K) = B(J))));

end Tab;

