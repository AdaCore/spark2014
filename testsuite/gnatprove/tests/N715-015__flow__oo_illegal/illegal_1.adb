package body Illegal_1 is
   overriding
   function New_Object return Extended_T is
      E : Extended_T;
   begin
      pragma Assert (G = 0);  --  Illegal. We cannot refer to G since
                              --  it was not a Proof_In of the overridden
                              --  function.
      Root.Object_T (E) := Root.New_Object;
      E.Y := 0;
      return E;
   end New_Object;

   overriding
   function New_Object (Input : Integer) return Extended_T is
      E : Extended_T;
   begin
      Root.Object_T (E) := Root.New_Object (Input);
      E.Y := Input;
      return E;
   end New_Object;

   overriding
   function New_Object_From_State return Extended_T is
      E : Extended_T;
   begin
      Root.Object_T (E) := Root.New_Object_From_State;
      E.Y := G;  --  Illegal. We cannot refer to G since
                 --  it was not an Input of the overriden
                 --  function.
      return E;
   end New_Object_From_State;

   overriding
   function New_P_Object return P_Extended_T is
      E : P_Extended_T;
   begin
      Root.P_Object_T (E) := Root.New_P_Object;
      E.Object_Y          := Extended_T'(X => 0,
                                         Y => 0);
      return E;
   end New_P_Object;

   overriding
   function New_P_Object (Input : Integer) return P_Extended_T is
      E : P_Extended_T;
   begin
      Root.P_Object_T (E) := Root.New_P_Object (Input);
      E.Object_Y          := Extended_T'(X => Input,
                                         Y => Input);
      return E;
   end New_P_Object;

   overriding
   function New_P_Object_From_State return P_Extended_T is
      E : P_Extended_T;
   begin
      Root.P_Object_T (E) := Root.New_P_Object_From_State;
      E.Object_Y          := Extended_T'(X => G,   --  Illegal
                                         Y => G);  --  Illegal
      --  We cannot refer to G since it was not an Input of
      --  the overridden function.
      return E;
   end New_P_Object_From_State;

   overriding
   procedure New_Object_And_Update_Global_Outputs (O : out Extended_T) is
   begin
      Root.Object_T (O) := Root.New_Object_From_State;
      O.Y := 0;
      if G < Integer'Last then  --  Illegal
         G := G + 1;            --  Illegal
      else
         G := Integer'First;    --  Illegal
      end if;
      --  G was not an In_Out of the overridden procedure so
      --  it cannot be an In_Out of this procedure.
   end New_Object_And_Update_Global_Outputs;

   overriding
   procedure Update_Global_Based_On_Object (O : Extended_T) is
   begin
      G := O.Y;  --  Illegal, G was not an Output of the overridden
                 --  procedure.
      --  Root.State was a global Output of the overridden procedure
      --  and is not an Output of this procedure.
   end Update_Global_Based_On_Object;

end Illegal_1;
