package P is
   subtype Index is Integer;
   type Arr is array (Index range 1 .. 10) of Integer;
   procedure Swap (A : in out Arr; J, K : Index) with
     Pre  => J in A'Range and K in A'Range,
     Post => A(J) = A(K)'Old and A(K) = A(J)'Old;
end P;
