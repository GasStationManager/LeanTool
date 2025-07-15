


WORKFLOW_DEFS = {
  'basic_fixing': '',

}

class Workflows:
    def __init__(self, workflow='basic_fixing'):
        self.sys_msg=WORKFLOW_DEFS.get(workflow, '')
