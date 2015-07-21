with Mode_Off;
package Mode_On with SPARK_Mode is
   type My_Array is new Mode_Off.My_Array;
   type My_Scalar is new Mode_Off.My_Scalar;
   type My_Record is new Mode_Off.My_Record;
end Mode_On;
