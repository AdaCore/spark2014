package body Power_14.Source_A_14
  with Refined_State => (State => S);
is
   S : Integer;

   procedure Read (Level : out Integer)
     with Refined_Global  => S,
          Refined_Depends => (Level => S)
   is
   begin
      Level := S;
   end Read;
end Power_14.Source_B_14;
