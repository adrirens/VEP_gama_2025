# example of bash code to run the batch simulations 

i=0

cd /opt/gama-platform

#./headless/gama-headless.sh -m 16g -hpc 15 -batch square_batch ~/Apps/Gama_Workspace/riot_simulation/simulations/simulation_square.gaml

#echo "WORK square_batch DONE"

./headless/gama-headless.sh -m 4g -hpc 5 -batch path_batch_calibration_$i ~/Apps/Gama_Workspace/ModelViolenceEmergenceInProtests/simulations/simulations_path/simulation_path_calibration_$i.gaml

echo "WORK path_batch DONE"

