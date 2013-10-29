package Global_Legal
  with SPARK_Mode,
       Abstract_State => (A1,
                          A2,
                          A3,
                          A4,
                          (A5 with External => Async_Readers),
                          (A6 with External),
                          (A7 with External => Async_Writers),
                          (A8 with External => (Async_Readers,
                                                Async_Writers)))
is
   type Rec is
      record
         A, B : Integer;
      end record;

   X : Integer;
   Comp : Rec;

   procedure P_Null (Par : Integer)
     --  global_specification ::= null
     with Global => null;

   procedure P_Global_Item (Par : Integer)
     --  global_specification ::= global_item
     with Global => X;

   procedure P_Many_Global_Items (Par : Integer)
     --  global_specification ::= global_item {, global_item}
     with Global => (X, A1, Comp, A2);

   procedure P_Moded_Global_List (Par : Integer)
     --  global_specification ::= moded_global_list
     with Global => (In_Out      => (X, A1, A2));

   procedure P_Many_Moded_Global_Lists (Par : Integer)
     --  global_specification ::= moded_global_list {, moded_global_list}
     with Global => (In_Out   => (A1, A2, A6, A8),
                     Input    => A7,
                     Output   => A5,
                     Proof_In => (A3, A4));

   function F_Null (Par : Integer) return Integer
     --  global_specification ::= null
     with Global => null;

   function F_Global_Item (Par : Integer) return Integer
     --  global_specification ::= global_item
     with Global => X;

   function F_Many_Global_Items (Par : Integer) return Integer
     --  global_specification ::= global_item {, global_item}
     with Global => (X, A1, Comp, A2);

   function F_Moded_Global_List (Par : Integer) return Integer
     --  global_specification ::= moded_global_list
     with Global => (Input    => (X, A1, Comp, A2));

   function F_Many_Moded_Global_Lists (Par : Integer) return Integer
     --  global_specification ::= moded_global_list {, moded_global_list}
     with Global => (Input    => (X, A1, Comp),
                     Proof_In => (A3, A4, A7));
end Global_Legal;
