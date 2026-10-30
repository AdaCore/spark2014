with Ada.Strings.Text_Buffers;

procedure Reject_Images with SPARK_Mode is
   package Images is
      type Number is new Integer with Put_Image => Put;
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Number) with SPARK_Mode => Off;
      type Derived is new Number;
      type Fixed is delta 0.125 range -10.0 .. 10.0 with Put_Image => Put;
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Fixed) with SPARK_Mode => Off;
      type Enumeration is (A, B) with Put_Image => Put;
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Enumeration) with SPARK_Mode => Off;
      type Derived_Enumeration is new Enumeration;
   end Images;

   package Private_Images is
      type Number is private;
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Number) with SPARK_Mode => Off;
   private
      type Number is new Integer with Put_Image => Put;
      type Derived is new Number;
      function Inherited_Aspect (X : Derived) return String is (Derived'Image (X));
   end Private_Images;

   package body Private_Images with SPARK_Mode => Off is
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Number) is null;
   end Private_Images;

   package body Images with SPARK_Mode => Off is
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Number) is null;
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Fixed) is null;
      procedure Put
        (Buffer : in out Ada.Strings.Text_Buffers.Root_Buffer_Type'Class;
         Value  : Enumeration) is null;
   end Images;

   function Direct (X : Images.Number) return String is (Images.Number'Image (X));
   function Object_Image (X : Images.Number) return String is (X'Image);
   function Object_Img (X : Images.Number) return String is (X'Img);
   function Inherited (X : Images.Derived) return String is
     (Images.Derived'Image (X));
   function Private_Aspect (X : Private_Images.Number) return String is
     (Private_Images.Number'Image (X));
   function Fixed_Image (X : Images.Fixed) return String is
     (Images.Fixed'Image (X));
   function Enumeration_Image (X : Images.Enumeration) return String is
     (Images.Enumeration'Image (X));
   function Inherited_Enumeration (X : Images.Derived_Enumeration) return String
   is (Images.Derived_Enumeration'Image (X));

   --  Fixed'Base is an itype without the first subtype's aspect. Its custom
   --  image is found through the type-specific subprogram lookup.

   function Base_Fixed_Image (X : Images.Fixed) return String is
     (Images.Fixed'Base'Image (X));
   function Base_Fixed_Object_Image (X : Images.Fixed'Base) return String is
     (X'Image);
   function Base_Fixed_Object_Img (X : Images.Fixed'Base) return String is
     (X'Img);
begin
   null;
end Reject_Images;
