package body Tests_External_State
  with SPARK_Mode,
       Refined_State => (State => Vol)
is
   Vol : Integer
     with Volatile;

   procedure Set (X : Integer)
     with Refined_Global  => (Output => Vol),
          Refined_Depends => (Vol => X)
   is
   begin
      Vol := X;
   end Set;

   procedure Get (X : out Integer)
     with Refined_Global  => (In_Out => Vol),
          Refined_Depends => ((X, Vol) => Vol)
   is
   begin
      X := Vol;
   end Get;
end Tests_External_State;
