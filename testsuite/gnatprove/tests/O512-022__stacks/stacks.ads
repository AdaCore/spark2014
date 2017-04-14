package Stacks is

   type Element is new Integer;
   type Elements is array (Integer range <>) of Element;

   type Stack (Max : Positive) is tagged private;

   function Is_Empty (S : Stack) return Boolean;
   pragma Test_Case (Name     => "empty stack",
                     Mode     => Nominal,
                     Requires => S.Size = 0,
                     Ensures  => Is_Empty'Result = True);
   pragma Test_Case (Name     => "non-empty stack",
                     Mode     => Nominal,
                     Requires => S.Size > 0,
                     Ensures  => Is_Empty'Result = False);

   function Is_Full (S : Stack) return Boolean;
   pragma Test_Case (Name     => "empty stack",
                     Mode     => Nominal,
                     Requires => S.Size = 0,
                     Ensures  => Is_Full'Result = False);

   function Size (S : Stack) return Natural;

   procedure Push (S : in out Stack; E : Element) with
     Pre'Class  => not S.Is_Full,
     Post'Class => S.Size = S.Size'Old + 1,
     Test_Case => (Name     => "full stack",
                   Mode     => Robustness,
                   Requires => S.Is_Full,
                   Ensures  => S.Size = S.Size'Old),
     Test_Case => (Name     => "almost empty stack",
                   Mode     => Nominal,
                   Requires => S.Is_Empty,
                   Ensures  => S.Size = 1),
     Test_Case => (Name     => "almost full stack",
                   Mode     => Nominal,
                   Requires => S.Size = S.Max - 1,
                   Ensures  => S.Is_Full),
     Test_Case => (Name     => "Nominal stack",
                   Mode     => Nominal,
                   Requires => S.Size >= 1 and then S.Size < S.Max - 1,
                   Ensures  => S.Size = S.Size'Old + 1);

   procedure Pop (S : in out Stack) with
     Pre'Class  => not S.Is_Empty,
     Post'Class => S.Size = S.Size'Old - 1,
     Test_Case => (Name     => "empty stack",
                   Mode     => Robustness,
                   Requires => S.Is_Empty,
                   Ensures  => S.Size = S.Size'Old),
     Test_Case => (Name     => "almost empty stack",
                   Mode     => Nominal,
                   Requires => S.Size = 1,
                   Ensures  => S.Is_Empty),
     Test_Case => (Name     => "almost full stack",
                   Mode     => Nominal,
                   Requires => S.Is_Full,
                   Ensures  => S.Size = S.Max - 1),
     Test_Case => (Name     => "Nominal stack",
                   Mode     => Nominal,
                   Requires => S.Size > 1 and then S.Size < S.Max,
                   Ensures  => S.Size = S.Size'Old - 1);

   function Peer (S : Stack) return Element with
     Pre'Class => not S.Is_Empty;

   procedure Print (S : Stack);

private

   type Stack (Max : Positive) is tagged record
      Top  : Natural;
      Data : Elements (1 .. Max);
   end record;

   function Size (S : Stack) return Natural is (S.Top);

   function Is_Empty (S : Stack) return Boolean is (S.Size = 0);

   function Is_Full (S : Stack) return Boolean is (S.Size = S.Max);

   function Peer (S : Stack) return Element is (S.Data (S.Top));

end Stacks;
