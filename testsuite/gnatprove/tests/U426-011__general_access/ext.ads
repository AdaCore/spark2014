package Ext with SPARK_Mode is
   type PS_Int is access Integer;
   type Gen_Int is access all Integer;
   type Cst_Int is access constant Integer;

   function F (X : Gen_Int) return Boolean with Import;
   function F (Dummy : Cst_Int) return Boolean is (True);

   X1 : PS_Int := new Integer'(12);           -- @RESOURCE_LEAK:NONE
   X2 : Gen_Int := new Integer'(12);          -- @RESOURCE_LEAK:FAIL
   X3 : Cst_Int := new Integer'(12);          -- @RESOURCE_LEAK:FAIL
   Y1 : constant Gen_Int := new Integer'(12); -- @RESOURCE_LEAK:NONE
   Y2 : constant Cst_Int := new Integer'(12); -- @RESOURCE_LEAK:NONE

   function Mk return Gen_Int with Import;
   W : Cst_Int := Cst_Int (Gen_Int'(new Integer'(15)));          -- @RESOURCE_LEAK:FAIL
   Z : constant Cst_Int := Cst_Int (Gen_Int'(new Integer'(15))); -- @RESOURCE_LEAK:NONE
   pragma Assert (F (Cst_Int (Gen_Int'(new Integer'(15)))));     -- @RESOURCE_LEAK:FAIL

   type Holder is record
      Content : PS_Int;
   end record;
   type Gen_Holder is access all Holder;

   P : Gen_Holder := new Holder'(Content => new Integer'(15));          -- @RESOURCE_LEAK:FAIL
   Q : constant Gen_Holder := new Holder'(Content => new Integer'(15)); -- @RESOURCE_LEAK:NONE

   type Rec_1 is record
      F : Cst_Int;
      G : Gen_Int;
      H : PS_Int;
   end record;
   type Rec_1_Arr is array (Positive range 1 .. 1) of Rec_1;

   function F (Dummy : Rec_1_Arr) return Boolean is (True);
   A1 : Rec_1_Arr :=(1 => (new Integer'(1),         -- @RESOURCE_LEAK:FAIL
                           new Integer'(1),         -- @RESOURCE_LEAK:FAIL
                           new Integer'(1)));       -- @RESOURCE_LEAK:NONE
   A2 : constant Rec_1_Arr :=(1 => (new Integer'(1),         -- @RESOURCE_LEAK:NONE
                                    new Integer'(1),         -- @RESOURCE_LEAK:NONE
                                    new Integer'(1)));       -- @RESOURCE_LEAK:NONE
   pragma Assert (F (Rec_1_Arr'(1 => (new Integer'(1),         -- @RESOURCE_LEAK:FAIL
                                      new Integer'(1),         -- @RESOURCE_LEAK:FAIL
                                      new Integer'(1)))));     -- @RESOURCE_LEAK:FAIL

   type Cst_Acc is access constant Rec_1;
   type Rec_2 is record
      F : Cst_Int;
      G : Gen_Int;
      H : Cst_Acc;
   end record;
   type Rec_2_Arr is array (Positive range 1 .. 1) of Rec_2;

   function F (Dummy : Rec_2_Arr) return Boolean is (True);
   B1 : Rec_2_Arr := (1 => (new Integer'(1),           -- @RESOURCE_LEAK:FAIL
                            new Integer'(1),           -- @RESOURCE_LEAK:FAIL
                            new Rec_1'                 -- @RESOURCE_LEAK:FAIL
                              (new Integer'(1),        -- @RESOURCE_LEAK:FAIL
                               new Integer'(1),        -- @RESOURCE_LEAK:FAIL
                               new Integer'(1))));     -- @RESOURCE_LEAK:NONE
   B2 : constant Rec_2_Arr := (1 => (new Integer'(1),           -- @RESOURCE_LEAK:NONE
                                     new Integer'(1),           -- @RESOURCE_LEAK:NONE
                                     new Rec_1'                 -- @RESOURCE_LEAK:NONE
                                       (new Integer'(1),        -- @RESOURCE_LEAK:NONE
                                        new Integer'(1),        -- @RESOURCE_LEAK:NONE
                                        new Integer'(1))));     -- @RESOURCE_LEAK:NONE
   pragma Assert (F (Rec_2_Arr'(1 => (new Integer'(1),           -- @RESOURCE_LEAK:FAIL
                                      new Integer'(1),           -- @RESOURCE_LEAK:FAIL
                                      new Rec_1'                 -- @RESOURCE_LEAK:FAIL
                                        (new Integer'(1),        -- @RESOURCE_LEAK:FAIL
                                         new Integer'(1),        -- @RESOURCE_LEAK:FAIL
                                         new Integer'(1))))));   -- @RESOURCE_LEAK:FAIL
end;
