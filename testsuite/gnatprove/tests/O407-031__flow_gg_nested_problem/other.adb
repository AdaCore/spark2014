with Nested_Problem;

package body Other is
   procedure A (N : in out Integer)
   is
   begin
      Nested_Problem.Level_1 (N);
   end A;

   procedure B (N : in out Integer)
   is
   begin
      Nested_Problem.Level_1 (N);
   end B;
end Other ;
