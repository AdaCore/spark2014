procedure Access_Conv with SPARK_Mode is
   type PS_Int is access Integer;
   type Gen_Int is access all Integer;
   type Cst_Int is access all Integer;

   function F (X : Gen_Int) return Boolean with
     Import,
     Global => null;
   function F (X : Cst_Int) return Boolean with
     Import,
     Global => null,
     Post => F'Result;

   type R is record
      F : Gen_Int;
   end record;
   type PS_R is access R;
   type Gen_R is access all R;

   type R_2 is record
      F : Gen_R;
   end record;

   X_1 : PS_Int := new Integer'(12);   -- @RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   B_1 : Boolean := F (Gen_Int (X_1)); -- @RESOURCE_LEAK:NONE
   Y_1 : R := (F => Gen_Int (X_1));    -- @RESOURCE_LEAK:FAIL

   X_2 : PS_Int := new Integer'(12);       -- @RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   Y_2 : R_2 := (F => new R'               -- @RESOURCE_LEAK:FAIL
                   (F => Gen_Int (X_2)));  -- @RESOURCE_LEAK:FAIL

   X_3 : PS_Int := new Integer'(12);        -- @RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   Y_3 : R_2 := (F => Gen_R (PS_R'(new R'   -- @RESOURCE_LEAK:FAIL
                   (F => Gen_Int (X_3))))); -- @RESOURCE_LEAK:FAIL

   type RC is record
      F : Cst_Int;
   end record;
   type PS_RC is access RC;
   type Cst_RC is access all RC;

   type RC_2 is record
      F : Cst_RC;
   end record;

   function C return PS_Int with
     Import,
     Global => null;

   X_4 : PS_Int := new Integer'(12);    -- @RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
   pragma Assert (F (Cst_Int (X_4)));   -- @RESOURCE_LEAK:NONE
   Y_4 : RC := (F => Cst_Int (C));      -- @RESOURCE_LEAK:FAIL

   Y_5 : RC_2 := (F => new RC'            -- @RESOURCE_LEAK:FAIL
                    (F => Cst_Int (C)));  -- @RESOURCE_LEAK:FAIL

   Y_6 : RC_2 := (F => Cst_RC (PS_RC'(new RC' -- @RESOURCE_LEAK:FAIL
                    (F => Cst_Int (C)))));    -- @RESOURCE_LEAK:FAIL

begin
   null;
end Access_Conv;
