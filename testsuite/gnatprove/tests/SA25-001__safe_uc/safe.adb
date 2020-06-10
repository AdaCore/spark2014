with Ada.Unchecked_Conversion;

procedure Safe is

   function To_Float_NO is new Ada.Unchecked_Conversion(Integer, Float); --@UNCHECKED_CONVERSION:FAIL

   function To_Nat_NO is new Ada.Unchecked_Conversion (Float, Natural);  --@UNCHECKED_CONVERSION:FAIL

   function To_Integer_NO is new Ada.Unchecked_Conversion (Float, Integer); --@UNCHECKED_CONVERSION:FAIL

   type Short_Short is range -128 .. 127;
   type U8 is mod 2 ** 8;

   type U7 is mod 2 ** 7;

   subtype SS_Nat is Short_Short range 0 .. 127;

   function To_U8_OK is new Ada.Unchecked_Conversion (Short_Short, U8);
   function To_SS_OK is new Ada.Unchecked_Conversion (U8, Short_Short);
   function To_SS_Nat_NO is new Ada.Unchecked_Conversion (U8, SS_Nat); --@UNCHECKED_CONVERSION:FAIL

   type HRec is record
      C      : Character;
      I      : Integer;
   end record;

   for Hrec use record
      C      at 0 range 0 .. 7;
      I      at 4 range 0 .. 31;
   end record;
   for Hrec'Object_Size use 64;

   type U64 is mod 2 ** 64;

   type HRec2 is record
      C      : Integer;
      I      : Integer;
   end record;
   for Hrec2'Object_Size use 64;

   function To_Hrec_NO is new Ada.Unchecked_Conversion (U64, Hrec); --@UNCHECKED_CONVERSION:FAIL

   function To_Hrec2_OK is new Ada.Unchecked_Conversion (U64, HRec2);

   type HRec3 is record
      C      : Character;
      I      : Integer;
   end record;

   function To_Hrec2_NO is new Ada.Unchecked_Conversion (U64, HRec3); --@UNCHECKED_CONVERSION:FAIL


   type Arr is array (1 .. 8) of Character;

   type Arr2 is array (1 .. 8) of Character;
   for Arr2'Object_Size use 64;

   function To_Arr_NO is new Ada.Unchecked_Conversion (U64, Arr); --@UNCHECKED_CONVERSION:FAIL
   function To_Arr_OK is new Ada.Unchecked_Conversion (U64, Arr2);


   type My_Enum is (E1, E2, E3, E4, E5, E6, E7, E8, E9,
                    E10, E20, E30, E40, E50, E60, E70, E80, E90,
                    E11, E21, E31, E41, E51, E61, E71, E81, E91,
                    E12, E22, E32, E42, E52, E62, E72, E82, E92,
                    E13, E23, E33, E43, E53, E63, E73, E83, E93,
                    E14, E24, E34, E44, E54, E64, E74, E84, E94,
                    E15, E25, E35, E45, E55, E65, E75, E85, E95,
                    E16, E26, E36, E46, E56, E66, E76, E86, E96,
                    E17, E27, E37, E47, E57, E67, E77, E87, E97,
                    E18, E28, E38, E48, E58, E68, E78, E88, E98,
                    E19, E29, E39, E49, E59, E69, E79, E89, E99,

                    E100, E101, E102, E103, E104, E105, E106, E107, E108, E109,

                    E110, E120, E130, E140, E150, E160, E170, E180, E190,
                    E111, E121, E131, E141, E151, E161, E171, E181, E191,
                    E112, E122, E132, E142, E152, E162, E172, E182, E192,
                    E113, E123, E133, E143, E153, E163, E173, E183, E193,
                    E114, E124, E134, E144, E154, E164, E174, E184, E194,
                    E115, E125, E135, E145, E155, E165, E175, E185, E195,
                    E116, E126, E136, E146, E156, E166, E176, E186, E196,
                    E117, E127, E137, E147, E157, E167, E177, E187, E197,
                    E118, E128, E138, E148, E158, E168, E178, E188, E198,
                    E119, E129, E139, E149, E159, E169, E179, E189, E199,

                    E200, E201, E202, E203, E204, E205, E206, E207, E208, E209,
                    E210, E220, E230, E240, E250,

                    E211, E221, E231, E241, E251,
                    E212, E222, E232, E242, E252,
                    E213, E223, E233, E243, E253,
                    E214, E224, E234, E244, E254,
                    E215, E225, E235, E245, E255,
                    E216, E226, E236, E246, E256,
                    E217, E227, E237, E247, 
                    E218, E228, E238, E248, 
                    E219, E229, E239, E249)
   with Object_Size => 8;

   type Enum_Num is range 0 .. 255
   with Object_Size => 8;

   subtype My_Enum_Sub is My_Enum range E1 .. E255;

   function Enum_OK is new Ada.Unchecked_Conversion (My_Enum, Enum_Num);
   function Enum_NO is new Ada.Unchecked_Conversion (My_Enum_Sub, Enum_Num); --@UNCHECKED_CONVERSION:FAIL

   type My_Rec (D : Character) is record
      X : Integer;
      case D is
         when 'A' =>
            Y : Integer;
         when 'B' =>
            Z : Integer;
         when others =>
            null;
      end case;
   end record;

   function Discr_NO is new Ada.Unchecked_Conversion (My_Rec, Integer); --@UNCHECKED_CONVERSION:FAIL

   function Size_NO is new Ada.Unchecked_Conversion (Integer, U8); --@UNCHECKED_CONVERSION_SIZE:FAIL

   
   type R is record
      A : U7;
      B : Boolean;
   end record
   with Object_Size => 8;

   function R_OK is new Ada.Unchecked_Conversion (U8, R);

begin
   null;
end Safe;
