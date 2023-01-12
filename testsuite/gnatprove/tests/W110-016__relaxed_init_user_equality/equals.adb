procedure equals with SPARK_mode is
   package P1 is
      type My_Int is new Integer with Relaxed_Initialization;

      type R is record
         I : Boolean;
         F : My_Int;
      end record with
        Predicate => (if I then F'Initialized);

      type H is record
        C : R;
      end record;

      type A is array(0..10) of R;

      --  "=" on H uses the predefined equality on R, so we need X.F and Y.F to
      --   be initialized here
      function Use_Eq (X, Y : H) return Boolean is (X = Y); --@INIT_BY_PROOF:FAIL
      function Use_Eq (X, Y : A) return Boolean is (X = Y); --@INIT_BY_PROOF:FAIL
   end P1;

   package P2 is
      type My_Int is new Integer with Relaxed_Initialization;

      type R is record
         I : Boolean;
         F : My_Int;
      end record with
        Predicate => (if I then F'Initialized);

      function "=" (X, Y : R) return Boolean is
        (X.I = Y.I and then (if X.I then X.F = Y.F));

      type H is record
        C : R;
      end record;
      type A is array(0..10) of R;

      --  "=" on H uses the redefined equality on R, so we don't need X.F and
      --   Y.F to be initialized here.
      function Use_Eq (X, Y : H) return Boolean is (X = Y); --  no initialization check required here
      function Use_Eq (X, Y : A) return Boolean is (X = Y); --  same
   end P2;
begin
   null;
end equals;
