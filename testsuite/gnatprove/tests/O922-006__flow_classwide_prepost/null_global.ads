package Null_Global is
   type Root is abstract tagged record
       F1 : Natural;
    end record;

    C : Natural := 0;

    procedure Check_F1 (R : Root) is abstract with
      Pre'Class => R.F1 = C;

    type Child is new Root with record
       F2 : Natural;
    end record;

    procedure Check_F1 (R : Child) with
      Global => null; --  We read C in Check_F1's Pre'Class

    procedure Check_F2 (R : Child) with
      Global    => null, --  We read C in Check_F2's Pre'Class
      Pre'Class => R.F2 = C;

    procedure Check_F1 (R : Child) is null;

    procedure Check_F2 (R : Child) is null;

end Null_Global;
