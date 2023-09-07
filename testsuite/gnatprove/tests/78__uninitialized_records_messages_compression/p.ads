package P with SPARK_Mode is

   My_Exception : exception;

   E : Boolean := True;

   type Empty is tagged record
      null;
   end record;

   type Rec_Natural is record
      A : Natural;
      B : Natural;
   end record;

   type Natural_And_Rec is record
      C : Natural;
      D : Rec_Natural;
   end record;

   type Normal_Only is tagged record
      A : Natural;
   end record;

   type Normal is new Normal_Only with record
      null;
   end record;

   type Normal_And_Private is new Normal_Only with private;

   type Other_Normal is record
      A : Natural;
   end record;

   type Rec is tagged record
      A : Other_Normal;
   end record;

   type Normal_Rec_And_Private is new Rec with private;

   type Private_Only is private;

   procedure Initialize_Empty_Class (R : out Empty'Class)
     with Always_Terminates;

   procedure Initialize_Normal (R : out Normal);

   procedure Initialize_Normal_Class (R : out Normal'Class)
     with Always_Terminates;

   procedure Initialize_Normal_Rec_And_Private (R: out Normal_Rec_And_Private);

   procedure Initialize_Normal_Private (R : out Normal_And_Private);

   procedure Initialize_Private (R : out Private_Only);

   procedure Initialize_Rec_Class (R : out Rec'Class) with Always_Terminates;

   procedure Raise_Exception (T : in out Natural_And_Rec)
        with Exceptional_Cases => (My_Exception => True);

   procedure Raise_Exception (T : in out Other_Normal)
        with Exceptional_Cases => (My_Exception => True);

private
   type Normal_And_Private is new Normal_Only with record
      B : Natural;
   end record;

   type Normal_Rec_And_Private is new Rec with record
      B : Natural;
   end record;

   type Private_Only is record
      B : Natural;
   end record;
end;
