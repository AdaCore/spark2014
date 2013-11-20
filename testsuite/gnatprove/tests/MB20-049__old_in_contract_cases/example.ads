package Example is

   type My_Array is array (1 .. 10) of Integer;
   subtype Value is Integer;

   procedure Extract (A : in out My_Array; J : Integer; V : out Value) with
     Contract_Cases => ((J in A'Range) => V = A(J)'Old and A(J) = 0,
                        others         => A = A'Old);

end Example;
