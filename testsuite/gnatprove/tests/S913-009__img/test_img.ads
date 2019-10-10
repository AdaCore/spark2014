package Test_Img with SPARK_mode is
function S (O : Natural) return String is (O'Img (O'Img'First + 1 .. O'Img'Last));
end Test_Img;
