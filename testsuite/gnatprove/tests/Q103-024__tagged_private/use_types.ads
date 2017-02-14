with Types; use Types;
package Use_Types with SPARK_Mode is
    type T is private;
    function Valid (X : T) return Boolean is (True);

private
    type T is new Types.T;
end Use_Types;
