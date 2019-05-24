with AA; use AA;

package A
with SPARK_Mode,
  Abstract_State => Global_AS
is

   --Global_A        : Natural ;
   subtype My_Natural is Natural;
   pragma Annotate (GNATprove, Init_By_Proof, My_Natural);


   procedure initGlobalsA(status : out Natural) with
   -- On BUILD, below line gives error: a.ads:14:35: "Global_A" is undefined
      Post => (if status = 0 then Global_A_Init),
     Global => (Output => Global_AS);

   -- On BUILD, below line gives error: a.ads:15:34: prefix of "Valid_Scalars" attribute must be object
   --  Post => (if status = 0 then Global_AS'Valid_Scalars);


  --@@@CPB   Global => (Output => (Global_AS, Global_AA));

   procedure UseA (X : in out Natural) with
   --@@@CPB  Pre => Global_A'Valid_Scalars,
     Global => (Input => Global_AS),
      Pre => Global_A_Init;
   --  Same as: "with Global => Global_Var;"

   function Global_A_Init return Boolean;

private

   Global_A        : My_Natural  with Part_Of => Global_AS;

   function Global_A_Init return Boolean is (Global_A'Valid_Scalars);


 --  Yet_Another_Global : Natural;
 --  pragma Annotate (GNATprove, Init_By_Proof, Yet_Another_Global);
end A;
