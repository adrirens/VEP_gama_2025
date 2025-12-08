# Model Violence Emergence in Protests (model VEP)

This model was presented at the JFSMA 2025 conference.

Folders and files:
- includes: you'll find generic models there. Especially computer_model.gaml is a personal library for mathematical computations that all agents need.
- models: you'll find the implemented models there. They are regrouped in species types (police_officers, citizens or unanimate for buildings and walls). The subfolder protest_configurations are here to set up the environment before the simulation begins.
- simulations: simulations_kettling, simulations_path, simulations_square and common_simulation.gaml are the folders or files of main interest. The folders contain the different experiments on separate files. This separation was done to ensure the configuration changed between simulations and to allow a better handling of computational resources. common_simulation.gaml has the very important data_recorder species implementation. It serves to record what happens during a simulation and send it to csv files automatically. simulations_agent_level was not implemented but the idea was to isolate agents with constant inputs and record their behavior. It was meant to analyze the stability and behavior of the model.

If you want to run a simulation, you may go to simulations/simulation_kettling/experiment_kettling_manual. The same kind of file is coded for the path scenario.


