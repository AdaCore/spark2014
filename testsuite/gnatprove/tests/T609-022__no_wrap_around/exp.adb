procedure Exp is
   type U8 is mod 2**8 with
     Annotate => (GNATprove, No_Wrap_Around);

   type U16 is mod 2**16 with
     Annotate => (GNATprove, No_Wrap_Around);

   type U32 is mod 2**32 with
     Annotate => (GNATprove, No_Wrap_Around);

   type U64 is mod 2**64 with
     Annotate => (GNATprove, No_Wrap_Around);

   procedure Succ (X8  : in out U8;
                   X16 : in out U16;
                   X32 : in out U32;
                   X64 : in out U64)
   with Post => X8 = X8'Old + 1   -- @OVERFLOW_CHECK:FAIL
            and X16 = X16'Old + 1 -- @OVERFLOW_CHECK:FAIL
            and X32 = X32'Old + 1 -- @OVERFLOW_CHECK:FAIL
            and X64 = X64'Old + 1 -- @OVERFLOW_CHECK:FAIL
   is
   begin
      X8  := U8'Succ  (X8);  -- @OVERFLOW_CHECK:FAIL
      X16 := U16'Succ (X16); -- @OVERFLOW_CHECK:FAIL
      X32 := U32'Succ (X32); -- @OVERFLOW_CHECK:FAIL
      X64 := U64'Succ (X64); -- @OVERFLOW_CHECK:FAIL
   end Succ;

   procedure OK_Succ (X8  : in out U8;
                      X16 : in out U16;
                      X32 : in out U32;
                      X64 : in out U64)
   with Pre  => X8 < U8'Last
            and X16 < U16'Last
            and X32 < U32'Last
            and X64 < U64'Last,
        Post => X8 = X8'Old + 1   -- @OVERFLOW_CHECK:PASS
            and X16 = X16'Old + 1 -- @OVERFLOW_CHECK:PASS
            and X32 = X32'Old + 1 -- @OVERFLOW_CHECK:PASS
            and X64 = X64'Old + 1 -- @OVERFLOW_CHECK:PASS
   is
   begin
      X8  := U8'Succ  (X8);  -- @OVERFLOW_CHECK:PASS
      X16 := U16'Succ (X16); -- @OVERFLOW_CHECK:PASS
      X32 := U32'Succ (X32); -- @OVERFLOW_CHECK:PASS
      X64 := U64'Succ (X64); -- @OVERFLOW_CHECK:PASS
   end OK_Succ;

   procedure Pred (X8  : in out U8;
                   X16 : in out U16;
                   X32 : in out U32;
                   X64 : in out U64)
   with Post => X8 = X8'Old - 1   -- @OVERFLOW_CHECK:FAIL
            and X16 = X16'Old - 1 -- @OVERFLOW_CHECK:FAIL
            and X32 = X32'Old - 1 -- @OVERFLOW_CHECK:FAIL
            and X64 = X64'Old - 1 -- @OVERFLOW_CHECK:FAIL
   is
   begin
      X8  := U8'Pred  (X8);  -- @OVERFLOW_CHECK:FAIL
      X16 := U16'Pred (X16); -- @OVERFLOW_CHECK:FAIL
      X32 := U32'Pred (X32); -- @OVERFLOW_CHECK:FAIL
      X64 := U64'Pred (X64); -- @OVERFLOW_CHECK:FAIL
   end Pred;

   procedure OK_Pred (X8  : in out U8;
                      X16 : in out U16;
                      X32 : in out U32;
                      X64 : in out U64)
   with Pre  => X8 > U8'First
            and X16 > U16'First
            and X32 > U32'First
            and X64 > U64'First,
        Post => X8 = X8'Old - 1   -- @OVERFLOW_CHECK:PASS
            and X16 = X16'Old - 1 -- @OVERFLOW_CHECK:PASS
            and X32 = X32'Old - 1 -- @OVERFLOW_CHECK:PASS
            and X64 = X64'Old - 1 -- @OVERFLOW_CHECK:PASS
   is
   begin
      X8  := U8'Pred  (X8);  -- @OVERFLOW_CHECK:PASS
      X16 := U16'Pred (X16); -- @OVERFLOW_CHECK:PASS
      X32 := U32'Pred (X32); -- @OVERFLOW_CHECK:PASS
      X64 := U64'Pred (X64); -- @OVERFLOW_CHECK:PASS
   end OK_Pred;

   procedure Expon (X8  : in out U8;
                    X16 : in out U16;
                    X32 : in out U32;
                    X64 : in out U64)
   with Post => X8 = X8'Old ** 3    -- @OVERFLOW_CHECK:FAIL
            and X16 = X16'Old ** 8  -- @OVERFLOW_CHECK:FAIL
            and X32 = X32'Old ** 16 -- @OVERFLOW_CHECK:FAIL
            and X64 = X64'Old ** 7  -- @OVERFLOW_CHECK:FAIL
   is
   begin
      X8  := X8 ** 3;   -- @OVERFLOW_CHECK:FAIL
      X16 := X16 ** 8;  -- @OVERFLOW_CHECK:FAIL
      X32 := X32 ** 16; -- @OVERFLOW_CHECK:FAIL
      X64 := X64 ** 7;  -- @OVERFLOW_CHECK:FAIL
   end Expon;

   procedure OK_Expon (X8  : in out U8;
                       X16 : in out U16;
                       X32 : in out U32;
                       X64 : in out U64)
   with Pre  => X8 <= 6
            and X16 <= 3
            and X32 <= 3
            and X64 <= 565,
        Post => X8 = X8'Old ** 3    -- @OVERFLOW_CHECK:PASS
            and X16 = X16'Old ** 8  -- @OVERFLOW_CHECK:PASS
            and X32 = X32'Old ** 16 -- @OVERFLOW_CHECK:PASS
            and X64 = X64'Old ** 7  -- @OVERFLOW_CHECK:PASS
   is
   begin
      X8  := X8 ** 3;   -- @OVERFLOW_CHECK:PASS
      X16 := X16 ** 8;  -- @OVERFLOW_CHECK:PASS
      X32 := X32 ** 16; -- @OVERFLOW_CHECK:PASS
      X64 := X64 ** 7;  -- @OVERFLOW_CHECK:PASS
   end OK_Expon;

   procedure Trivial_Expon (X8  : in out U8;
                            X16 : in out U16;
                            X32 : in out U32;
                            X64 : in out U64)
   with Post => X8 = X8'Old
            and X16 = X16'Old
            and X32 = X32'Old
            and X64 = X64'Old
   is
   begin
      if X8 in 0 .. 1 then
         X8  := X8 ** 3;   -- @OVERFLOW_CHECK:PASS
      end if;
      if X16 in 0 .. 1 then
         X16 := X16 ** 8;  -- @OVERFLOW_CHECK:PASS
      end if;
      if X32 in 0 .. 1 then
         X32 := X32 ** 16; -- @OVERFLOW_CHECK:PASS
      end if;
      if X64 in 0 .. 1 then
         X64 := X64 ** 7;  -- @OVERFLOW_CHECK:PASS
      end if;
   end Trivial_Expon;

   X8  : U8 := 0;
   X16 : U16 := 0;
   X32 : U32 := 0;
   X64 : U64 := 0;
begin
   Succ (X8, X16, X32, X64);
   OK_Succ (X8, X16, X32, X64);
   Pred (X8, X16, X32, X64);
   OK_Pred (X8, X16, X32, X64);
   Expon (X8, X16, X32, X64);
   OK_Expon (X8, X16, X32, X64);
   Trivial_Expon (X8, X16, X32, X64);
end Exp;
