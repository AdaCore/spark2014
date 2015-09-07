pragma SPARK_Mode(On);
package List_Handler -- To demonstrate instantiation of generic package
   with
      Abstract_State => List,
      Initializes    => List
is
   procedure Append_Range (Lower, Upper : in Integer)
      with
         Global  => (In_Out => List),
         Depends => (List =>+ (Lower, Upper));
end List_Handler;
