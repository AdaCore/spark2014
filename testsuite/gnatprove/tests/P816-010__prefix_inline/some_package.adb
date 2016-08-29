with Generic_Queue;

pragma Elaborate_All (Generic_Queue);

package body Some_Package with SPARK_Mode is

   type MyElement is new Float range 0.0 .. 10.0 with Default_Value => 0.0;
   package Float_Buffer is new Generic_Queue(Index_Type   => Unsigned_8,
                                             Element_Type => MyElement);
   use Float_Buffer;
   Buf_Handle : Float_Buffer.Buffer_Tag;

   procedure foo is
   begin
      Buf_Handle.push_back (1.2);
      Buf_Handle.push_back (1.3);
   end foo;

   procedure bar is
   begin
      foo;
   end bar;

end Some_Package;
