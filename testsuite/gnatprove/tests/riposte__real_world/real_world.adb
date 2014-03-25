package body Real_World is

   type Enum_A is (A_01, A_02, A_03, A_04, A_05, A_06,
                   A_07, A_08, A_09, A_10, A_11, A_12);

   type Enum_B is (B_01, B_02, B_03, B_04, B_05, B_06);

   type T is (E_A, E_B, E_C, E_D, E_E);

   function Example_A (Sort : in Enum_A) return Enum_B
     with Post => (if Sort = A_03 then Example_A'Result = B_04)
                     and (if Sort = A_05 then Example_A'Result = B_02)
                     and (if (Sort = A_06)
                            or (Sort = A_10)
                            or (Sort = A_07)
                            or (Sort = A_08)
                          then Example_A'Result = B_03)
                     and (if Sort = A_02 then Example_A'Result = B_05)
                     and (if Sort = A_09 then Example_A'Result = B_06)
                     and (if (Sort = A_01)
                            or (Sort = A_04)
                            or (Sort = A_11)
                            or (Sort = A_12)
                          then Example_A'Result = B_01)
   is
      R : Enum_B;
   begin
      case Sort is
         when A_03                      => R := B_04;
         when A_05                      => R := B_02;
         when A_06 | A_10 | A_07 | A_08 => R := B_03;
         when A_02                      => R := B_05;
         when A_09                      => R := B_06;
         when others                    => R := B_01;
      end case;
      return R;
   end Example_A;


   function Simplifier_Problems (Param : in T) return T
     with Pre => Param = E_B or Param = E_D
   is
   begin
      pragma Assert (Param < E_E);  --  @ASSERT:PASS
      return T'Succ(Param);
   end Simplifier_Problems;

   function K616_030_A (X  : in Integer;
                        Y  : in Integer;
                        Z  : in Integer;
                        C  : in Integer;
                        C2 : in Integer)
                       return Boolean
     with Depends => (K616_030_A'Result => (X, C2),
                      null => (Y, Z, C)),
          Pre     => X + Y <= Z and Z <= C and C2 + Y >= C,
          Post    => K616_030_A'Result = True  --  @POSTCONDITION:PASS
   is
   begin
      return X <= C2;
   end K616_030_A;

   function K616_030_B (X  : in Integer;
                        Y  : in Integer;
                        Z  : in Integer;
                        C  : in Integer;
                        C2 : in Integer)
                       return Boolean
     with Depends => (K616_030_B'Result => (X, C2),
                      null => (Y, Z, C)),
          Pre  => X - Y >= Z and Z >= C and C2 - Y <= C,
          Post => K616_030_B'Result = True  --  @POSTCONDITION:PASS
   is
   begin
      return X >= C2;
   end K616_030_B;

end Real_World;
