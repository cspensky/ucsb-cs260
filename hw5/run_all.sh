sbt compile

for f in tests/*.lwnn
do
	echo -e "\e[0;34m"    
	echo "Running $f.."
	echo -e "\e[0;35m"
	cat $f
	echo -e "\e[m"
	sbt "run $f"
done
