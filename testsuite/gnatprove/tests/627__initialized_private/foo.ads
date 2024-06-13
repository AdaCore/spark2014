with Bounded_String_80;

package Foo is
   subtype File_Name_Type is Bounded_String_80.Bounded_String_Base;
   procedure Read_Packet
      (Data : out File_Name_Type)
   with Relaxed_Initialization => Data,
        Post => Data'Initialized;
end;
