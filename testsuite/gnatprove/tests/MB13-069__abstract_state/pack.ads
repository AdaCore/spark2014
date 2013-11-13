pragma SPARK_Mode;

package Pack with
  Abstract_State => Content
is
   procedure Update_Content with
     Global => (In_Out => Content);
end Pack;
